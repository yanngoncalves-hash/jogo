#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
DOOMFIST - Arena de socos 3D (raycasting estilo Doom) com multiplayer em LAN.

Como jogar:
    pip install pygame
    python doomfist.py                 -> menu (Hospedar / Entrar)
    python doomfist.py host [nome]     -> hospeda uma partida e joga
    python doomfist.py join IP [nome]  -> entra na partida de alguem
    python doomfist.py server          -> servidor dedicado (sem janela de jogo)

Controles:
    W A S D / setas ..... andar        Mouse / setas esq-dir ... olhar
    Botao esquerdo / ESPACO ........... SOCO
    Botao direito / SHIFT (segurar) ... DEFESA (reduz 85% do dano)
    Botao direito / SHIFT (APERTAR NA HORA CERTA) ... PARRY!
        -> se o soco do inimigo acertar durante a janela do parry, voce nao
           toma dano, o atacante fica atordoado e voce ganha contra-ataque (dano x1.6).
        -> o parry tem cooldown, nao adianta spammar.
    TAB ... placar        ESC ... sair
"""
import sys
import math
import json
import time
import socket
import threading
import random
from array import array

import pygame

# ----------------------------------------------------------------------------
# Configuracoes
# ----------------------------------------------------------------------------
PORT = 5555
TICK_RATE = 60

# Combate (tempos em segundos)
PUNCH_T = 0.45        # duracao total do soco
HIT_T = 0.16          # momento em que o soco acerta
RANGE = 1.35          # alcance do soco
ARC = 0.65            # angulo (rad) de cada lado em que o soco acerta
PARRY_WIN = 0.22      # janela de parry apos apertar defesa
PARRY_CD = 0.80       # cooldown do parry
PARRY_STUN = 1.10     # atordoamento do atacante parriado
DMG = 14
CHIP = 2              # dano ao acertar uma defesa normal
COUNTER_MULT = 1.6    # multiplicador de dano em alvo atordoado
RESPAWN = 3.0
MAXHP = 100

# Render
W, H = 320, 200       # resolucao interna (pixelada, estilo Doom)
SCALE = 3
SW, SH = W * SCALE, H * SCALE
FOV = math.radians(66)
PL = math.tan(FOV / 2)
TEX = 64
NL = 12               # niveis de sombreamento por distancia

COLORS = [(220, 50, 50), (50, 120, 230), (60, 200, 90), (240, 200, 50),
          (180, 70, 220), (240, 130, 40), (60, 210, 210), (230, 230, 230)]

# ----------------------------------------------------------------------------
# Mapa
# ----------------------------------------------------------------------------
MW = MH = 24
MAP = [[1 if x in (0, MW - 1) or y in (0, MH - 1) else 0 for x in range(MW)] for y in range(MH)]


def _rect(x0, y0, x1, y1, t):
    for yy in range(y0, y1 + 1):
        for xx in range(x0, x1 + 1):
            MAP[yy][xx] = t


# pilares
_rect(5, 5, 6, 6, 2)
_rect(17, 5, 18, 6, 2)
_rect(5, 17, 6, 18, 2)
_rect(17, 17, 18, 18, 2)
# sala central (com aberturas nos cantos)
_rect(10, 8, 13, 8, 3)
_rect(10, 15, 13, 15, 3)
_rect(8, 10, 8, 13, 3)
_rect(15, 10, 15, 13, 3)
# blocos
_rect(2, 11, 3, 12, 1)
_rect(20, 11, 21, 12, 1)
_rect(11, 2, 12, 3, 1)
_rect(11, 20, 12, 21, 1)

SPAWNS = [(2.5, 2.5), (21.5, 2.5), (2.5, 21.5), (21.5, 21.5),
          (12.0, 5.5), (12.0, 18.5), (5.5, 12.0), (18.5, 12.0)]


def angdiff(a, b):
    return (a - b + math.pi) % (2 * math.pi) - math.pi


def blocked(x, y, r=0.25):
    for cx in (x - r, x + r):
        for cy in (y - r, y + r):
            if MAP[int(cy)][int(cx)]:
                return True
    return False


def local_ip():
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))
        return s.getsockname()[0]
    except OSError:
        return "127.0.0.1"
    finally:
        s.close()


# ----------------------------------------------------------------------------
# SERVIDOR (autoritativo: movimento, socos, defesa, parry, vida)
# ----------------------------------------------------------------------------
class Player:
    def __init__(self, pid, color):
        self.id = pid
        self.name = "P%d" % pid
        self.color = color
        self.x, self.y, self.a = 2.5, 2.5, 0.0
        self.hp = MAXHP
        self.f = self.s = 0.0
        self.blk_held = False
        self.press_t = -9.0
        self.bt = -1.0          # tempo desde que comecou a defender (-1 = nao defende)
        self.pcd = 0.0          # cooldown do parry
        self.pt = -1.0          # tempo do soco (-1 = nao socando)
        self.punch_req = 0.0
        self.last_pc = 0
        self.stun = 0.0
        self.hit_t = 0.0
        self.dead_t = -1.0
        self.kx = self.ky = 0.0
        self.kills = self.deaths = 0


class Server:
    def __init__(self, port=PORT):
        self.port = port
        self.lock = threading.Lock()
        self.players = {}
        self.clients = {}
        self.events = []
        self.next_id = 1

    def start(self):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        self.sock.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        self.sock.bind(("0.0.0.0", self.port))
        self.sock.listen(8)
        threading.Thread(target=self.accept_loop, daemon=True).start()
        threading.Thread(target=self.tick_loop, daemon=True).start()

    # --- rede ---
    def accept_loop(self):
        while True:
            try:
                conn, _ = self.sock.accept()
            except OSError:
                return
            threading.Thread(target=self.client_loop, args=(conn,), daemon=True).start()

    def client_loop(self, conn):
        conn.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        conn.settimeout(5.0)
        with self.lock:
            pid = self.next_id
            self.next_id += 1
            p = Player(pid, (pid - 1) % len(COLORS))
            self.players[pid] = p
            self.respawn(p)
        try:
            conn.sendall((json.dumps({"t": "w", "id": pid}) + "\n").encode())
        except OSError:
            with self.lock:
                self.players.pop(pid, None)
            return
        with self.lock:
            self.clients[pid] = conn
        buf = b""
        try:
            while True:
                try:
                    data = conn.recv(4096)
                except socket.timeout:
                    continue
                if not data:
                    break
                buf += data
                while b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    try:
                        self.handle(pid, json.loads(line))
                    except (ValueError, KeyError, TypeError):
                        pass
        except OSError:
            pass
        finally:
            with self.lock:
                self.players.pop(pid, None)
                self.clients.pop(pid, None)
            try:
                conn.close()
            except OSError:
                pass

    def handle(self, pid, m):
        with self.lock:
            p = self.players.get(pid)
            if not p:
                return
            t = m.get("t")
            if t == "h":
                p.name = str(m.get("n", p.name))[:12] or p.name
            elif t == "i":
                p.f = max(-1.0, min(1.0, float(m["f"])))
                p.s = max(-1.0, min(1.0, float(m["s"])))
                p.a = float(m["a"])
                pc = int(m["pc"])
                if pc > p.last_pc:
                    p.last_pc = pc
                    p.punch_req = 0.3
                b = bool(m["b"])
                if b and not p.blk_held:
                    p.press_t = time.perf_counter()
                p.blk_held = b

    # --- simulacao ---
    def respawn(self, p):
        others = [q for q in self.players.values() if q is not p and q.dead_t < 0]

        def score(s):
            return min([(s[0] - q.x) ** 2 + (s[1] - q.y) ** 2 for q in others] or [999])

        p.x, p.y = max(SPAWNS, key=score)
        p.a = math.atan2(12 - p.y, 12 - p.x)
        p.hp = MAXHP
        p.dead_t = -1.0
        p.bt = p.pt = -1.0
        p.stun = p.hit_t = p.kx = p.ky = 0.0
        p.punch_req = 0.0

    def los(self, a, b):
        for i in range(1, 6):
            t = i / 6.0
            if MAP[int(a.y + (b.y - a.y) * t)][int(a.x + (b.x - a.x) * t)]:
                return False
        return True

    def damage(self, v, a, dmg):
        v.hp -= dmg
        v.hit_t = 0.25
        v.pt = -1.0
        d = math.atan2(v.y - a.y, v.x - a.x)
        v.kx, v.ky = math.cos(d) * 4.5, math.sin(d) * 4.5
        self.events.append(["hit", a.id, v.id])
        if v.hp <= 0:
            v.hp = 0
            v.dead_t = 0.0
            v.bt = -1.0
            v.deaths += 1
            a.kills += 1
            self.events.append(["kill", a.id, v.id])

    def resolve_punch(self, a):
        best, bd = None, RANGE
        for v in self.players.values():
            if v is a or v.dead_t >= 0:
                continue
            dx, dy = v.x - a.x, v.y - a.y
            d = math.hypot(dx, dy)
            if d > bd or abs(angdiff(math.atan2(dy, dx), a.a)) > ARC or not self.los(a, v):
                continue
            best, bd = v, d
        if best is None:
            return
        v = best
        facing = abs(angdiff(math.atan2(a.y - v.y, a.x - v.x), v.a)) < 1.3
        if v.bt >= 0 and facing:
            if v.bt <= PARRY_WIN:                      # ===== PARRY =====
                a.stun = PARRY_STUN
                a.pt = -1.0
                a.punch_req = 0.0
                d = math.atan2(a.y - v.y, a.x - v.x)
                a.kx, a.ky = math.cos(d) * 3.5, math.sin(d) * 3.5
                v.pcd = 0.0                            # recompensa: parry pronto de novo
                self.events.append(["parry", v.id, a.id])
            else:                                      # defesa normal
                a.stun = max(a.stun, 0.25)
                d = math.atan2(v.y - a.y, v.x - a.x)
                v.kx, v.ky = math.cos(d) * 2.0, math.sin(d) * 2.0
                self.events.append(["block", v.id, a.id])
                v.hp -= CHIP
                if v.hp <= 0:
                    v.hp = 1
        else:
            dmg = DMG * (COUNTER_MULT if v.stun > 0 else 1.0)
            self.damage(v, a, dmg)

    def move(self, p, dx, dy):
        nx = p.x + dx
        if not blocked(nx, p.y):
            p.x = nx
        ny = p.y + dy
        if not blocked(p.x, ny):
            p.y = ny

    def step(self, dt, now):
        with self.lock:
            ps = list(self.players.values())
            for p in ps:
                if p.dead_t >= 0:
                    p.dead_t += dt
                    if p.dead_t >= RESPAWN:
                        self.respawn(p)
                    continue
                p.pcd = max(0.0, p.pcd - dt)
                p.stun = max(0.0, p.stun - dt)
                p.hit_t = max(0.0, p.hit_t - dt)
                p.punch_req = max(0.0, p.punch_req - dt)

                # progresso do soco
                if p.pt >= 0:
                    old = p.pt
                    p.pt += dt
                    if old < HIT_T <= p.pt:
                        self.resolve_punch(p)
                    if p.pt >= PUNCH_T:
                        p.pt = -1.0

                # defesa / parry
                want_block = p.blk_held or (now - p.press_t) < 0.09
                can_act = p.stun <= 0 and p.pt < 0
                if want_block and can_act:
                    if p.bt < 0:
                        if (now - p.press_t) < 0.15 and p.pcd <= 0:
                            p.bt = 0.0
                            p.pcd = PARRY_CD
                        else:
                            p.bt = PARRY_WIN + 0.01
                    else:
                        p.bt += dt
                else:
                    p.bt = -1.0

                # iniciar soco
                if p.pt < 0 and p.bt < 0 and p.stun <= 0 and p.punch_req > 0 and not want_block:
                    p.pt = 0.0
                    p.punch_req = 0.0
                    self.events.append(["punch", p.id, 0])

                # movimento
                speed = 3.2
                if p.bt >= 0:
                    speed = 1.6
                if p.pt >= 0:
                    speed = 1.0
                if p.stun > 0:
                    speed = 0.0
                dx, dy = math.cos(p.a), math.sin(p.a)
                vx = dx * p.f - dy * p.s
                vy = dy * p.f + dx * p.s
                m = math.hypot(vx, vy)
                if m > 1:
                    vx, vy = vx / m, vy / m
                self.move(p, (vx * speed + p.kx) * dt, (vy * speed + p.ky) * dt)
                p.kx *= max(0.0, 1 - 9 * dt)
                p.ky *= max(0.0, 1 - 9 * dt)

            # separacao entre jogadores
            alive = [p for p in ps if p.dead_t < 0]
            for i in range(len(alive)):
                for j in range(i + 1, len(alive)):
                    a, b = alive[i], alive[j]
                    dx, dy = b.x - a.x, b.y - a.y
                    d = math.hypot(dx, dy)
                    if 0 < d < 0.55:
                        push = (0.55 - d) / 2
                        ux, uy = dx / d, dy / d
                        self.move(a, -ux * push, -uy * push)
                        self.move(b, ux * push, uy * push)

    def snapshot(self):
        with self.lock:
            pl = [{"i": p.id, "n": p.name, "c": p.color,
                   "x": round(p.x, 3), "y": round(p.y, 3), "a": round(p.a, 3),
                   "h": int(p.hp), "pt": round(p.pt, 3), "bt": round(p.bt, 3),
                   "st": p.stun > 0, "d": p.dead_t >= 0, "k": p.kills, "dt": p.deaths,
                   "ht": p.hit_t > 0, "pc": round(p.pcd, 2)} for p in self.players.values()]
            ev, self.events = self.events, []
            clients = list(self.clients.items())
        return (json.dumps({"t": "s", "p": pl, "e": ev}) + "\n").encode(), clients

    def tick_loop(self):
        dt = 1.0 / TICK_RATE
        nxt = time.perf_counter()
        last = nxt
        while True:
            now = time.perf_counter()
            self.step(min(0.1, now - last), now)
            last = now
            msg, clients = self.snapshot()
            for pid, c in clients:
                try:
                    c.sendall(msg)
                except OSError:
                    with self.lock:
                        self.clients.pop(pid, None)
            nxt += dt
            delay = nxt - time.perf_counter()
            if delay > 0:
                time.sleep(delay)
            else:
                nxt = time.perf_counter()


# ----------------------------------------------------------------------------
# CLIENTE - rede
# ----------------------------------------------------------------------------
class Net:
    def __init__(self, host, port, name):
        self.sock = socket.create_connection((host, port), timeout=5)
        self.sock.settimeout(None)
        self.sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        self.lock = threading.Lock()
        self.snap = None
        self.events = []
        self.id = None
        self.alive = True
        threading.Thread(target=self.reader, daemon=True).start()
        self.send({"t": "h", "n": name})

    def reader(self):
        buf = b""
        try:
            while True:
                d = self.sock.recv(65536)
                if not d:
                    break
                buf += d
                while b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    m = json.loads(line)
                    if m["t"] == "w":
                        self.id = m["id"]
                    elif m["t"] == "s":
                        with self.lock:
                            self.snap = m["p"]
                            self.events += m["e"]
        except (OSError, ValueError):
            pass
        self.alive = False

    def send(self, m):
        try:
            self.sock.sendall((json.dumps(m) + "\n").encode())
        except OSError:
            self.alive = False


# ----------------------------------------------------------------------------
# GRAFICOS: texturas, fundo, sprites
# ----------------------------------------------------------------------------
def _clamp(v):
    return max(0, min(255, int(v)))


def make_tex(kind):
    s = pygame.Surface((TEX, TEX))
    rnd = random.Random(kind * 77)
    if kind == 1:        # tijolos
        base, mortar = (150, 62, 45), (62, 38, 32)
        s.fill(mortar)
        for row in range(8):
            y, off = row * 8, (row % 2) * 8
            for bx in range(-1, 5):
                sh = rnd.randint(-22, 18)
                col = (_clamp(base[0] + sh), _clamp(base[1] + sh * 0.5), _clamp(base[2] + sh * 0.4))
                pygame.draw.rect(s, col, (bx * 16 + off + 1, y + 1, 14, 6))
    elif kind == 2:      # pedra
        s.fill((40, 44, 56))
        for row in range(4):
            y, off = row * 16, (row % 2) * 16
            for bx in range(-1, 3):
                sh = rnd.randint(-14, 14)
                col = (_clamp(95 + sh), _clamp(100 + sh), _clamp(118 + sh))
                pygame.draw.rect(s, col, (bx * 32 + off + 1, y + 1, 30, 14))
    else:                # painel tecnologico
        s.fill((38, 62, 48))
        for px_ in range(2):
            for py_ in range(2):
                x, y = px_ * 32, py_ * 32
                pygame.draw.rect(s, (70, 110, 88), (x + 2, y + 2, 28, 28))
                pygame.draw.rect(s, (28, 44, 36), (x + 2, y + 2, 28, 28), 2)
                for cx, cy in ((x + 5, y + 5), (x + 27, y + 5), (x + 5, y + 27), (x + 27, y + 27)):
                    pygame.draw.circle(s, (170, 180, 170), (cx, cy), 1)
        for k in range(0, TEX, 8):
            pygame.draw.rect(s, (220, 190, 40), (k, 30, 4, 4))
    for _ in range(160):
        x, y = rnd.randrange(TEX), rnd.randrange(TEX)
        c = s.get_at((x, y))
        d = rnd.randint(-18, 10)
        s.set_at((x, y), (_clamp(c[0] + d), _clamp(c[1] + d), _clamp(c[2] + d)))
    return s


def build_textures():
    cols = {}
    for t in (1, 2, 3):
        base = make_tex(t)
        for side in (0, 1):
            for lvl in range(NL):
                sh = base.copy()
                f = (1 - lvl / NL * 0.93) * (1.0 if side == 0 else 0.72)
                v = int(255 * f)
                sh.fill((v, v, v), special_flags=pygame.BLEND_RGB_MULT)
                cols[(t, side, lvl)] = [sh.subsurface((x, 0, 1, TEX)) for x in range(TEX)]
    return cols


def build_bg():
    bg = pygame.Surface((W, H))
    for y in range(H // 2):
        k = y / (H / 2)
        pygame.draw.line(bg, (int(12 + 26 * (1 - k)), int(12 + 24 * (1 - k)), int(20 + 34 * (1 - k))), (0, y), (W, y))
    for y in range(H // 2, H):
        k = (y - H / 2) / (H / 2)
        pygame.draw.line(bg, (int(26 + 50 * k), int(23 + 42 * k), int(20 + 34 * k)), (0, y), (W, y))
    return bg


SKIN = (230, 180, 140)


def make_sprite(col, state):
    s = pygame.Surface((32, 64), pygame.SRCALPHA)
    dark = tuple(int(c * 0.6) for c in col)
    pants = (40, 40, 62)
    pygame.draw.rect(s, pants, (10, 44, 5, 20))
    pygame.draw.rect(s, pants, (17, 44, 5, 20))
    pygame.draw.rect(s, (25, 25, 30), (9, 60, 6, 4))
    pygame.draw.rect(s, (25, 25, 30), (17, 60, 6, 4))
    pygame.draw.rect(s, col, (8, 22, 16, 24))
    pygame.draw.rect(s, dark, (8, 22, 16, 24), 1)
    pygame.draw.circle(s, SKIN, (16, 12), 7)
    pygame.draw.rect(s, dark, (9, 5, 14, 3))
    pygame.draw.rect(s, (10, 10, 10), (13, 10, 2, 2))
    pygame.draw.rect(s, (10, 10, 10), (18, 10, 2, 2))

    def fist(x, y, r):
        pygame.draw.circle(s, (110, 60, 40), (x, y), r + 1)
        pygame.draw.circle(s, SKIN, (x, y), r)

    if state in ("idle", "hit"):
        pygame.draw.line(s, col, (8, 25), (7, 31), 4)
        pygame.draw.line(s, col, (24, 25), (25, 31), 4)
        fist(7, 33, 4)
        fist(25, 33, 4)
    elif state == "punch":
        pygame.draw.line(s, col, (8, 25), (7, 31), 4)
        fist(7, 33, 4)
        pygame.draw.line(s, col, (23, 25), (17, 30), 5)
        fist(16, 31, 9)
    elif state in ("block", "parry"):
        pygame.draw.line(s, SKIN, (8, 34), (14, 16), 5)
        pygame.draw.line(s, SKIN, (24, 34), (18, 16), 5)
        fist(14, 14, 4)
        fist(18, 14, 4)
        if state == "parry":
            pygame.draw.circle(s, (120, 240, 255), (16, 24), 15, 2)
            pygame.draw.circle(s, (220, 255, 255), (16, 24), 11, 1)
    elif state == "stun":
        pygame.draw.line(s, col, (8, 25), (6, 40), 4)
        pygame.draw.line(s, col, (24, 25), (26, 40), 4)
        fist(6, 42, 4)
        fist(26, 42, 4)
        for sx, sy in ((6, 3), (16, 0), (26, 4)):
            pygame.draw.line(s, (255, 230, 60), (sx - 2, sy), (sx + 2, sy), 1)
            pygame.draw.line(s, (255, 230, 60), (sx, sy - 2), (sx, sy + 2), 1)
    if state == "hit":
        s.fill((110, 0, 0, 0), special_flags=pygame.BLEND_RGB_ADD)
    return s


def build_sprites():
    d = {}
    for ci, col in enumerate(COLORS):
        for st in ("idle", "hit", "punch", "block", "parry", "stun"):
            d[(ci, st)] = make_sprite(col, st)
    return d


def sprite_state(p):
    if p["st"]:
        return "stun"
    if p["pt"] >= 0.04:
        return "punch"
    if p["bt"] >= 0:
        return "parry" if p["bt"] <= PARRY_WIN else "block"
    if p["ht"]:
        return "hit"
    return "idle"


# ----------------------------------------------------------------------------
# RENDER 3D (raycasting)
# ----------------------------------------------------------------------------
def render_walls(low, bg, texcols, px, py, ang, zbuf):
    low.blit(bg, (0, 0))
    dx, dy = math.cos(ang), math.sin(ang)
    plx, ply = -dy * PL, dx * PL
    scale = pygame.transform.scale
    for x in range(W):
        cam = 2.0 * x / W - 1.0
        rdx, rdy = dx + plx * cam, dy + ply * cam
        mx, my = int(px), int(py)
        ddx = abs(1.0 / rdx) if rdx else 1e30
        ddy = abs(1.0 / rdy) if rdy else 1e30
        if rdx < 0:
            stx, sdx = -1, (px - mx) * ddx
        else:
            stx, sdx = 1, (mx + 1.0 - px) * ddx
        if rdy < 0:
            sty, sdy = -1, (py - my) * ddy
        else:
            sty, sdy = 1, (my + 1.0 - py) * ddy
        while True:
            if sdx < sdy:
                sdx += ddx
                mx += stx
                side = 0
            else:
                sdy += ddy
                my += sty
                side = 1
            tile = MAP[my][mx]
            if tile:
                break
        if side == 0:
            perp = sdx - ddx
            wx = py + perp * rdy
        else:
            perp = sdy - ddy
            wx = px + perp * rdx
        if perp < 0.02:
            perp = 0.02
        zbuf[x] = perp
        wx -= math.floor(wx)
        tx = int(wx * TEX)
        if (side == 0 and rdx > 0) or (side == 1 and rdy < 0):
            tx = TEX - 1 - tx
        lvl = int(perp * 0.6)
        if lvl >= NL:
            lvl = NL - 1
        col = texcols[(tile, side, lvl)][tx]
        lh = int(H / perp)
        if lh <= H:
            low.blit(scale(col, (1, max(1, lh))), (x, (H - lh) // 2))
        else:
            vis = TEX * H / lh
            y0 = int((TEX - vis) / 2)
            low.blit(scale(col.subsurface((0, y0, 1, max(1, int(vis)))), (1, H)), (x, 0))


def render_sprites(low, px, py, ang, players, sm, zbuf, me_id, sprs):
    dx, dy = math.cos(ang), math.sin(ang)
    plx, ply = -dy * PL, dx * PL
    inv = 1.0 / (plx * dy - dx * ply)
    items = []
    for p in players:
        if p["i"] == me_id or p["d"] or p["i"] not in sm:
            continue
        x, y = sm[p["i"]]
        sx, sy = x - px, y - py
        ty = inv * (-ply * sx + plx * sy)
        tx = inv * (dy * sx - dx * sy)
        if ty < 0.2:
            continue
        items.append((ty, tx, p))
    items.sort(key=lambda t: -t[0])
    labels = []
    for ty, tx, p in items:
        scx = int(W / 2 * (1 + tx / ty))
        lh = H / ty
        sh = int(lh * 0.9)
        sw = sh // 2
        if sh < 4 or sw < 2:
            continue
        top = int(H / 2 + lh / 2) - sh
        img = pygame.transform.scale(sprs[(p["c"], sprite_state(p))], (sw, sh))
        v = int(255 * max(0.2, 1 - ty / 22))
        img.fill((v, v, v), special_flags=pygame.BLEND_RGB_MULT)
        x0 = scx - sw // 2
        for i in range(sw):
            X = x0 + i
            if 0 <= X < W and zbuf[X] > ty:
                low.blit(img, (X, top), (i, 0, 1, sh))
        if 0 <= scx < W and zbuf[scx] > ty:
            labels.append((scx * SCALE, top * SCALE, p, ty))
    return labels


def _fist(surf, cx, cy, r, col=SKIN):
    pygame.draw.circle(surf, (110, 60, 40), (cx, cy), r + 2)
    pygame.draw.circle(surf, col, (cx, cy), r)
    for k in (-1, 0, 1):
        pygame.draw.line(surf, (190, 135, 100), (cx + k * r // 2, cy - r // 2), (cx + k * r // 2, cy - 1), 1)


def _arm(surf, bx, fx, fy, r):
    pygame.draw.polygon(surf, (60, 70, 120), [(bx - 26, H), (bx + 26, H),
                                              (fx + r * 0.8, fy + r * 0.6), (fx - r * 0.8, fy + r * 0.6)])
    pygame.draw.polygon(surf, (35, 40, 80), [(bx - 26, H), (bx + 26, H),
                                             (fx + r * 0.8, fy + r * 0.6), (fx - r * 0.8, fy + r * 0.6)], 1)


def draw_fists(low, me, hand, t, moving):
    bob = math.sin(t * 7) * 3 if moving else 0
    bobx, boby = int(bob), int(abs(bob))
    L = [85 + bobx, 168 + boby, 18]
    R = [235 - bobx, 168 + boby, 18]
    if me["st"]:
        sway = int(math.sin(t * 6) * 6)
        for f in (L, R):
            f[1] += 24
        L[0] += sway
        R[0] += sway
    if me["bt"] >= 0:                               # defendendo
        parry = me["bt"] <= PARRY_WIN
        col = (160, 235, 255) if parry else SKIN
        for bx, fx in ((80, 135), (240, 185)):
            _arm(low, bx, fx, 118, 20)
            _fist(low, fx, 116, 20, col)
        if parry:
            r = int(75 - me["bt"] / PARRY_WIN * 28)
            pygame.draw.circle(low, (120, 240, 255), (W // 2, 112), r, 3)
            pygame.draw.circle(low, (230, 255, 255), (W // 2, 112), max(4, r - 6), 1)
        return
    punching = me["pt"] >= 0
    for i, f in enumerate((L, R)):
        if punching and i == hand:
            continue
        _arm(low, f[0] - (10 if i == 0 else -10), f[0], f[1], f[2])
        _fist(low, f[0], f[1], f[2])
    if punching:
        u = min(1.0, me["pt"] / PUNCH_T)
        e = math.sin(math.pi * u)
        rest = R if hand == 1 else L
        tx = W // 2 + (14 if hand == 1 else -14)
        x = int(rest[0] + (tx - rest[0]) * e)
        y = int(rest[1] + (92 - rest[1]) * e)
        r = int(18 + 20 * e)
        _arm(low, rest[0] + (10 if hand == 1 else -10), x, y, r)
        _fist(low, x, y, r)


# ----------------------------------------------------------------------------
# SOM (gerado por codigo, sem arquivos)
# ----------------------------------------------------------------------------
RATE = 22050


def tone(freqs, dur, vol, decay, noise=0.0):
    n = int(RATE * dur)
    buf = array('h')
    for i in range(n):
        t = i / RATE
        env = math.exp(-decay * t)
        v = sum(math.sin(2 * math.pi * f * t) for f in freqs) / len(freqs) if freqs else 0.0
        v = v * (1 - noise) + random.uniform(-1, 1) * noise
        buf.append(int(max(-1.0, min(1.0, v * env * vol)) * 32767))
    return pygame.mixer.Sound(buffer=buf.tobytes())


def make_sounds():
    try:
        return {
            "punch": tone([], 0.18, 0.35, 14, 1.0),
            "hit": tone([90, 60], 0.28, 0.9, 11, 0.35),
            "block": tone([220, 150], 0.18, 0.6, 22, 0.5),
            "parry": tone([1250, 1880, 2500], 0.55, 0.5, 6, 0.05),
            "kill": tone([55, 40], 0.6, 0.9, 5, 0.3),
        }
    except Exception:
        return {}


# ----------------------------------------------------------------------------
# MENU
# ----------------------------------------------------------------------------
def menu(screen, clock, err=""):
    big = pygame.font.Font(None, 110)
    font = pygame.font.Font(None, 34)
    small = pygame.font.Font(None, 24)
    fields = ["Jogador%d" % random.randint(1, 99), "127.0.0.1"]
    labels = ["Nome", "IP do host (para entrar)"]
    active = 0
    btn_host = pygame.Rect(SW // 2 - 330, 430, 300, 60)
    btn_join = pygame.Rect(SW // 2 + 30, 430, 300, 60)
    pygame.mouse.set_visible(True)
    pygame.event.set_grab(False)
    while True:
        for e in pygame.event.get():
            if e.type == pygame.QUIT:
                return None
            if e.type == pygame.KEYDOWN:
                if e.key == pygame.K_ESCAPE:
                    return None
                elif e.key == pygame.K_TAB:
                    active ^= 1
                elif e.key == pygame.K_BACKSPACE:
                    fields[active] = fields[active][:-1]
                elif e.key == pygame.K_F1:
                    return ("host", fields[0], fields[1])
                elif e.key in (pygame.K_F2, pygame.K_RETURN):
                    return ("join", fields[0], fields[1])
                elif e.unicode and e.unicode.isprintable() and len(fields[active]) < 20:
                    fields[active] += e.unicode
            if e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
                if btn_host.collidepoint(e.pos):
                    return ("host", fields[0], fields[1])
                if btn_join.collidepoint(e.pos):
                    return ("join", fields[0], fields[1])
                for i in range(2):
                    if pygame.Rect(SW // 2 - 250, 210 + i * 100, 500, 44).collidepoint(e.pos):
                        active = i
        screen.fill((18, 8, 8))
        for i in range(0, SH, 6):
            pygame.draw.line(screen, (30 + (i * 40) // SH, 8, 8), (0, i), (SW, i))
        t = big.render("DOOMFIST", True, (230, 40, 30))
        screen.blit(t, (SW // 2 - t.get_width() // 2, 60))
        s = small.render("Arena de socos 3D em LAN  -  soco / defesa / PARRY", True, (230, 200, 160))
        screen.blit(s, (SW // 2 - s.get_width() // 2, 150))
        for i in range(2):
            lab = small.render(labels[i], True, (200, 200, 200))
            screen.blit(lab, (SW // 2 - 250, 186 + i * 100))
            r = pygame.Rect(SW // 2 - 250, 210 + i * 100, 500, 44)
            pygame.draw.rect(screen, (40, 20, 20), r)
            pygame.draw.rect(screen, (255, 200, 60) if i == active else (110, 70, 60), r, 2)
            txt = font.render(fields[i] + ("_" if i == active and int(time.time() * 2) % 2 else ""), True, (255, 255, 255))
            screen.blit(txt, (r.x + 10, r.y + 10))
        for r, label in ((btn_host, "HOSPEDAR  (F1)"), (btn_join, "ENTRAR  (F2 / Enter)")):
            pygame.draw.rect(screen, (140, 25, 20), r)
            pygame.draw.rect(screen, (255, 120, 60), r, 3)
            tt = font.render(label, True, (255, 255, 255))
            screen.blit(tt, (r.centerx - tt.get_width() // 2, r.centery - tt.get_height() // 2))
        info = small.render("Seu IP na LAN: %s   |   Porta: %d   |   TAB troca de campo" % (local_ip(), PORT), True, (180, 180, 180))
        screen.blit(info, (SW // 2 - info.get_width() // 2, 520))
        if err:
            e_ = small.render(err, True, (255, 90, 90))
            screen.blit(e_, (SW // 2 - e_.get_width() // 2, 555))
        pygame.display.flip()
        clock.tick(30)


# ----------------------------------------------------------------------------
# JOGO (cliente)
# ----------------------------------------------------------------------------
def game(screen, clock, net, host_ip=None):
    pygame.mouse.set_visible(False)
    pygame.event.set_grab(True)
    pygame.mouse.get_rel()

    f_small = pygame.font.Font(None, 22)
    f_mid = pygame.font.Font(None, 32)
    f_big = pygame.font.Font(None, 84)

    low = pygame.Surface((W, H))
    big = pygame.Surface((SW, SH))
    flash = pygame.Surface((SW, SH), pygame.SRCALPHA)
    bg = build_bg()
    texcols = build_textures()
    sprs = build_sprites()
    sounds = make_sounds()
    zbuf = [0.0] * W

    # minimapa pre-renderizado
    cell = 5
    mini = pygame.Surface((MW * cell, MH * cell))
    tcol = {0: (20, 20, 20), 1: (150, 62, 45), 2: (100, 105, 125), 3: (70, 110, 88)}
    for y in range(MH):
        for x in range(MW):
            pygame.draw.rect(mini, tcol[MAP[y][x]], (x * cell, y * cell, cell, cell))
    mini.set_alpha(190)

    ang = 0.0
    pc = 0
    sm = {}
    snap = []
    prev_dead = True
    prev_pt = -1.0
    hand = 0
    shake = 0.0
    flash_col, flash_a = (255, 0, 0), 0.0
    msg_txt, msg_col, msg_t = "", (255, 255, 255), 0.0
    hitmark = 0.0
    feed = []
    t0 = time.time()
    first = True
    running = True

    def say(txt, col, dur=0.9):
        nonlocal msg_txt, msg_col, msg_t
        msg_txt, msg_col, msg_t = txt, col, dur

    def play(name, pos, me_pos):
        s = sounds.get(name)
        if not s:
            return
        d = math.hypot(pos[0] - me_pos[0], pos[1] - me_pos[1])
        v = max(0.0, 1 - d / 12)
        if v > 0.02:
            s.set_volume(v)
            s.play()

    while running and net.alive:
        dt = min(clock.tick(60) / 1000.0, 0.05)
        now = time.time()

        for e in pygame.event.get():
            if e.type == pygame.QUIT:
                running = False
            elif e.type == pygame.KEYDOWN:
                if e.key == pygame.K_ESCAPE:
                    running = False
                elif e.key in (pygame.K_SPACE, pygame.K_f):
                    pc += 1
            elif e.type == pygame.MOUSEBUTTONDOWN and e.button == 1:
                pc += 1

        mx, _ = pygame.mouse.get_rel()
        if first:
            mx, first = 0, False
        ang += mx * 0.0024
        keys = pygame.key.get_pressed()
        if keys[pygame.K_LEFT]:
            ang -= 2.4 * dt
        if keys[pygame.K_RIGHT]:
            ang += 2.4 * dt
        f = int(keys[pygame.K_w] or keys[pygame.K_UP]) - int(keys[pygame.K_s] or keys[pygame.K_DOWN])
        s = int(keys[pygame.K_d]) - int(keys[pygame.K_a])
        block = bool(pygame.mouse.get_pressed()[2] or keys[pygame.K_LSHIFT] or keys[pygame.K_RSHIFT])
        net.send({"t": "i", "f": f, "s": s, "a": round(ang, 4), "pc": pc, "b": block})

        with net.lock:
            if net.snap is not None:
                snap = net.snap
            evs, net.events = net.events, []
        byid = {p["i"]: p for p in snap}
        me = byid.get(net.id)

        # suavizacao de posicao
        k = 1 - math.exp(-dt * 30)
        for p in snap:
            c = sm.get(p["i"])
            if c is None or abs(c[0] - p["x"]) + abs(c[1] - p["y"]) > 2:
                sm[p["i"]] = [p["x"], p["y"]]
            else:
                c[0] += (p["x"] - c[0]) * k
                c[1] += (p["y"] - c[1]) * k
        for pid in list(sm):
            if pid not in byid:
                del sm[pid]
        if me is None:
            screen.fill((0, 0, 0))
            t = f_mid.render("Conectando...", True, (255, 255, 255))
            screen.blit(t, (SW // 2 - t.get_width() // 2, SH // 2))
            pygame.display.flip()
            continue

        mypos = sm[me["i"]]
        if prev_dead and not me["d"]:
            ang = math.atan2(12 - mypos[1], 12 - mypos[0])
        prev_dead = me["d"]
        if prev_pt < 0 <= me["pt"]:
            hand ^= 1
        prev_pt = me["pt"]

        # eventos
        for ev in evs:
            kind, a, b = ev
            na = byid.get(a, {}).get("n", "?")
            nb = byid.get(b, {}).get("n", "?")
            pos = sm.get(a, mypos)
            if kind == "punch":
                play("punch", pos, mypos)
            elif kind == "hit":
                play("hit", sm.get(b, mypos), mypos)
                if b == me["i"]:
                    flash_col, flash_a, shake = (255, 0, 0), 150, 10
                if a == me["i"]:
                    hitmark = 0.18
            elif kind == "block":
                play("block", pos, mypos)
                if a == me["i"]:
                    say("BLOQUEADO", (200, 200, 200), 0.6)
                    shake = 4
                elif b == me["i"]:
                    say("Voce bloqueou", (200, 200, 200), 0.5)
                    shake = 3
            elif kind == "parry":
                play("parry", pos, mypos)
                if a == me["i"]:
                    say("PARRY!", (120, 240, 255), 1.0)
                    flash_col, flash_a, shake = (120, 240, 255), 120, 6
                elif b == me["i"]:
                    say("VOCE FOI PARRIADO!", (255, 120, 80), 1.0)
                    shake = 12
            elif kind == "kill":
                play("kill", sm.get(b, mypos), mypos)
                feed.append(("%s nocauteou %s" % (na, nb), now + 5))

        # render 3D
        render_walls(low, bg, texcols, mypos[0], mypos[1], ang, zbuf)
        labels = render_sprites(low, mypos[0], mypos[1], ang, snap, sm, zbuf, me["i"], sprs)
        if not me["d"]:
            moving = (f != 0 or s != 0) and me["pt"] < 0
            draw_fists(low, me, hand, now - t0, moving)

        pygame.transform.scale(low, (SW, SH), big)
        shake = max(0.0, shake - 40 * dt)
        ox = int(random.uniform(-shake, shake))
        oy = int(random.uniform(-shake, shake))
        screen.fill((0, 0, 0))
        screen.blit(big, (ox, oy))

        # nomes e barras de vida acima dos inimigos
        for lx, ly, p, ty in labels:
            nm = f_small.render(p["n"], True, COLORS[p["c"]])
            screen.blit(nm, (lx - nm.get_width() // 2, ly - 24))
            bw = 44
            pygame.draw.rect(screen, (60, 0, 0), (lx - bw // 2, ly - 8, bw, 5))
            pygame.draw.rect(screen, (60, 220, 60), (lx - bw // 2, ly - 8, int(bw * p["h"] / MAXHP), 5))

        # flash de tela
        if flash_a > 0:
            flash.fill((*flash_col, int(flash_a)))
            screen.blit(flash, (0, 0))
            flash_a = max(0, flash_a - 420 * dt)
        if me["d"]:
            flash.fill((120, 0, 0, 140))
            screen.blit(flash, (0, 0))
            t = f_big.render("VOCE FOI NOCAUTEADO", True, (255, 220, 200))
            screen.blit(t, (SW // 2 - t.get_width() // 2, SH // 2 - 60))
            t = f_mid.render("renascendo...", True, (255, 255, 255))
            screen.blit(t, (SW // 2 - t.get_width() // 2, SH // 2 + 20))

        # mira
        cx, cy = SW // 2, SH // 2
        pygame.draw.line(screen, (255, 255, 255), (cx - 8, cy), (cx - 3, cy), 2)
        pygame.draw.line(screen, (255, 255, 255), (cx + 3, cy), (cx + 8, cy), 2)
        pygame.draw.line(screen, (255, 255, 255), (cx, cy - 8), (cx, cy - 3), 2)
        pygame.draw.line(screen, (255, 255, 255), (cx, cy + 3), (cx, cy + 8), 2)
        if hitmark > 0:
            hitmark -= dt
            for sx_, sy_ in ((-1, -1), (1, -1), (-1, 1), (1, 1)):
                pygame.draw.line(screen, (255, 60, 60), (cx + sx_ * 8, cy + sy_ * 8), (cx + sx_ * 18, cy + sy_ * 18), 3)

        # mensagem central
        if msg_t > 0:
            msg_t -= dt
            t = f_big.render(msg_txt, True, msg_col)
            screen.blit(t, (SW // 2 - t.get_width() // 2, SH // 2 - 160))
        if me["st"]:
            t = f_mid.render("ATORDOADO!", True, (255, 230, 60))
            screen.blit(t, (SW // 2 - t.get_width() // 2, SH // 2 + 90))

        # HUD: vida
        pygame.draw.rect(screen, (30, 0, 0), (20, SH - 44, 260, 26))
        pygame.draw.rect(screen, (200, 30, 30), (20, SH - 44, int(260 * me["h"] / MAXHP), 26))
        pygame.draw.rect(screen, (255, 255, 255), (20, SH - 44, 260, 26), 2)
        t = f_mid.render("VIDA %d" % me["h"], True, (255, 255, 255))
        screen.blit(t, (28, SH - 41))
        # HUD: parry
        ready = 1 - min(1.0, me["pc"] / PARRY_CD)
        pygame.draw.rect(screen, (10, 25, 30), (SW // 2 - 90, SH - 40, 180, 16))
        pygame.draw.rect(screen, (120, 240, 255) if ready >= 1 else (70, 110, 120),
                         (SW // 2 - 90, SH - 40, int(180 * ready), 16))
        pygame.draw.rect(screen, (200, 240, 250), (SW // 2 - 90, SH - 40, 180, 16), 1)
        t = f_small.render("PARRY PRONTO" if ready >= 1 else "PARRY...", True, (220, 250, 255))
        screen.blit(t, (SW // 2 - t.get_width() // 2, SH - 62))
        # HUD: kills
        t = f_mid.render("Nocautes: %d   Mortes: %d" % (me["k"], me["dt"]), True, (255, 230, 150))
        screen.blit(t, (SW - t.get_width() - 20, SH - 40))

        # minimapa
        screen.blit(mini, (10, 10))
        for p in snap:
            if p["d"] or p["i"] not in sm:
                continue
            x, y = sm[p["i"]]
            pygame.draw.circle(screen, COLORS[p["c"]], (10 + int(x * cell), 10 + int(y * cell)), 3)
        mx_, my_ = 10 + int(mypos[0] * cell), 10 + int(mypos[1] * cell)
        pygame.draw.line(screen, (255, 255, 255), (mx_, my_),
                         (mx_ + int(math.cos(ang) * 9), my_ + int(math.sin(ang) * 9)), 2)

        # kill feed
        feed = [x for x in feed if x[1] > now]
        for i, (txt, _) in enumerate(feed[-5:]):
            t = f_small.render(txt, True, (255, 255, 255))
            screen.blit(t, (SW - t.get_width() - 14, 12 + i * 22))

        # ajuda inicial
        if now - t0 < 20:
            lines = ["WASD: andar | Mouse: olhar | Botao esq/ESPACO: SOCO",
                     "Botao dir/SHIFT: segurar = DEFESA | APERTAR quando o soco chegar = PARRY",
                     "TAB: placar | ESC: sair"]
            if host_ip:
                lines.insert(0, "Voce e o HOST. Os outros entram com o IP: %s (porta %d)" % (host_ip, PORT))
            for i, ln in enumerate(lines):
                t = f_small.render(ln, True, (255, 255, 200))
                screen.blit(t, (SW // 2 - t.get_width() // 2, 12 + i * 20))

        # placar
        if keys[pygame.K_TAB]:
            panel = pygame.Surface((520, 60 + 30 * len(snap)), pygame.SRCALPHA)
            panel.fill((0, 0, 0, 190))
            screen.blit(panel, (SW // 2 - 260, 140))
            t = f_mid.render("PLACAR", True, (255, 220, 120))
            screen.blit(t, (SW // 2 - t.get_width() // 2, 150))
            for i, p in enumerate(sorted(snap, key=lambda q: -q["k"])):
                t = f_mid.render("%-12s   nocautes %2d    mortes %2d" % (p["n"], p["k"], p["dt"]), True, COLORS[p["c"]])
                screen.blit(t, (SW // 2 - 240, 190 + i * 30))

        pygame.display.flip()

    pygame.event.set_grab(False)
    pygame.mouse.set_visible(True)
    return net.alive is False and running


# ----------------------------------------------------------------------------
# MAIN
# ----------------------------------------------------------------------------
def main():
    args = sys.argv[1:]
    if args and args[0] == "server":
        srv = Server(PORT)
        srv.start()
        print("Servidor DOOMFIST rodando em %s:%d  (Ctrl+C para parar)" % (local_ip(), PORT))
        try:
            while True:
                time.sleep(1)
        except KeyboardInterrupt:
            return

    try:
        pygame.mixer.pre_init(RATE, -16, 1, 512)
    except Exception:
        pass
    pygame.init()
    pygame.display.set_caption("DOOMFIST - Arena de socos")
    screen = pygame.display.set_mode((SW, SH))
    clock = pygame.time.Clock()

    preset = None
    if args and args[0] == "host":
        preset = ("host", args[1] if len(args) > 1 else "Host", "127.0.0.1")
    elif args and args[0] == "join" and len(args) > 1:
        preset = ("join", args[2] if len(args) > 2 else "Jogador", args[1])

    err = ""
    while True:
        choice = preset or menu(screen, clock, err)
        preset = None
        if not choice:
            break
        mode, name, ip = choice
        host_ip = None
        try:
            if mode == "host":
                srv = Server(PORT)
                srv.start()
                ip = "127.0.0.1"
                host_ip = local_ip()
            net = Net(ip.strip(), PORT, name.strip() or "Jogador")
        except OSError as ex:
            err = "Erro: %s" % ex
            continue
        lost = game(screen, clock, net, host_ip)
        if lost:
            err = "Conexao com o servidor perdida."
            continue
        break
    pygame.quit()


if __name__ == "__main__":
    main()
