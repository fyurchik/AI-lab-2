#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
ЛР №2, «Системи штучного інтелекту».
Сліпий пошук на графах: пошук в глибину (DFS) і пошук в ширину (BFS)
з графічним інтерфейсом (Tkinter) для їх порівняння.

Керування мишею: лівий клік по полотну виконує дію, обрану на панелі
«Редагування» (додати/видалити вершину, з'єднати, видалити зв'язок,
змінити напрямок).
Запуск: python search_lab.py
"""

import math
import time
import tkinter as tk
from collections import deque
from tkinter import ttk, messagebox

# ---------------------------------------------------------------------------
# Заданий граф: 31 вершина, 43 ребра, 6 гілок, фіксовані координати.
# Пара (u, v) в орграфі означає дугу u -> v.
# ---------------------------------------------------------------------------
VERTICES = {
    1: (450, 355),
    2: (540, 355), 3: (620, 355), 4: (693, 415), 5: (693, 295), 6: (762, 433),
    7: (501, 273), 8: (541, 204), 9: (630, 171), 10: (525, 111), 11: (680, 119),
    12: (400, 282), 13: (360, 213), 14: (376, 120), 15: (271, 180), 16: (356, 50),
    17: (364, 361), 18: (284, 361), 19: (211, 301), 20: (211, 421), 21: (142, 283),
    22: (399, 430), 23: (359, 499), 24: (270, 532), 25: (375, 592), 26: (220, 584),
    27: (500, 427), 28: (540, 496), 29: (524, 589), 30: (629, 529), 31: (544, 659),
}
EDGES = [
    (1, 2), (2, 3), (3, 4), (3, 5), (4, 6),
    (1, 7), (7, 8), (8, 9), (8, 10), (9, 11),
    (12, 1), (13, 12), (14, 13), (15, 13), (16, 14),
    (17, 1), (18, 17), (19, 18), (20, 18), (21, 19),
    (1, 22), (22, 23), (23, 24), (23, 25), (24, 26),
    (27, 1), (28, 27), (29, 28), (30, 28), (31, 29),
    (5, 9), (10, 14), (15, 19), (20, 24), (25, 29), (30, 4),
    (3, 8), (13, 18), (23, 28), (10, 11), (21, 20), (31, 30), (7, 12),
]
START, GOAL = 21, 9

METHODS = {"dfs": "в глибину", "bfs": "в ширину"}

ORDERS = {
    "asc": "за зростанням номерів",
    "desc": "за спаданням номерів",
    "cw": "за годинниковою стрілкою",
    "ccw": "проти годинникової стрілки",
}
R = 15  # радіус вершини


# ---------------------------------------------------------------------------
# Модель графа
# ---------------------------------------------------------------------------
class Graph:
    def __init__(self):
        self.pos = dict(VERTICES)
        self.edges = {e: False for e in EDGES}   # (u, v) -> True, якщо дуга u->v

    def copy(self):
        g = Graph()
        g.pos, g.edges = dict(self.pos), dict(self.edges)
        return g

    def find(self, a, b):
        if (a, b) in self.edges:
            return (a, b)
        if (b, a) in self.edges:
            return (b, a)
        return None

    def components(self):
        adj = {v: set() for v in self.pos}
        for u, v in self.edges:
            adj[u].add(v)
            adj[v].add(u)
        seen, comps = set(), []
        for s in self.pos:
            if s in seen:
                continue
            q, comp = [s], {s}
            seen.add(s)
            while q:
                x = q.pop()
                for y in adj[x] - seen:
                    seen.add(y)
                    comp.add(y)
                    q.append(y)
            comps.append(comp)
        return comps

    def kind(self):
        arcs = sum(self.edges.values())
        if arcs and arcs == len(self.edges):
            return "орграф"
        if arcs:
            return "змішаний граф"
        if self.pos and len(self.edges) == len(self.pos) - 1 and len(self.components()) == 1:
            return "дерево"
        return "звичайний граф"

    def add_vertex(self, x, y):
        v = 1
        while v in self.pos:
            v += 1
        self.pos[v] = (int(x), int(y))
        return v

    def remove_vertex(self, v):
        del self.pos[v]
        self.edges = {k: d for k, d in self.edges.items() if v not in k}

    def neighbors(self, v, order):
        """Наступники вершини v у заданому порядку обходу."""
        out = []
        for (a, b), d in self.edges.items():
            if a == v:
                out.append(b)
            elif b == v and not d:
                out.append(a)
        if order == "asc":
            return sorted(out)
        if order == "desc":
            return sorted(out, reverse=True)
        x0, y0 = self.pos[v]

        def angle(w):  # кут від напрямку «на 12 годин» за годинниковою стрілкою
            x, y = self.pos[w]
            a = math.atan2(x - x0, y0 - y) % (2 * math.pi)
            return a if order == "cw" else (2 * math.pi - a) % (2 * math.pi)
        return sorted(out, key=angle)

    def spanning_tree(self, root):
        t = self.copy()
        t.edges = {}
        seen, q = {root}, deque([root])
        while q:
            x = q.popleft()
            for (a, b) in self.edges:
                y = b if a == x else a if b == x else None
                if y is not None and y not in seen:
                    seen.add(y)
                    t.edges[(x, y)] = False
                    q.append(y)
        return t


# ---------------------------------------------------------------------------
# Пошук в ширину
# ---------------------------------------------------------------------------
def search(g, start, goal, order, method="dfs"):
    """
    Сліпий пошук на графі зі списками OPEN і CLOSED.
      method="bfs" — пошук в ширину: OPEN — черга (FIFO), нові вершини в КІНЕЦЬ;
      method="dfs" — пошук в глибину: OPEN — стек (LIFO), нові вершини на ПОЧАТОК.
    Повертає шлях, кількість циклів, розкритих і породжених вершин та кроки для анімації.
    """
    parent = {start: None}
    open_q, closed = deque([start]), []
    cycles = expanded = 0
    found = start == goal
    steps = []
    while open_q and not found:
        cycles += 1                      # цикл: вибір першої вершини з OPEN
        n = open_q.popleft()
        closed.append(n)
        expanded += 1                    # розкриття: породження наступників
        born = []
        for m in g.neighbors(n, order):
            if m in parent:              # вже в OPEN або CLOSED
                continue
            parent[m] = n
            born.append(m)
            if m == goal:
                found = True
                break
        if not found:
            if method == "bfs":
                open_q.extend(born)                  # у кінець черги
            else:
                open_q.extendleft(reversed(born))    # на вершину стеку (перший сусід — першим)
        steps.append((n, born, list(open_q), list(closed)))
    path = []
    if found:
        v = goal
        while v is not None:
            path.append(v)
            v = parent[v]
        path.reverse()
    return {"path": path, "cycles": cycles, "expanded": expanded,
            "generated": len(parent), "steps": steps, "parent": parent}


def search_time_us(g, start, goal, order, method):
    """Час одного пошуку, мкс (медіана 5 серій по 50 запусків)."""
    res = []
    for _ in range(5):
        t0 = time.perf_counter()
        for _ in range(50):
            search(g, start, goal, order, method)
        res.append((time.perf_counter() - t0) / 50 * 1e6)
    return sorted(res)[2]


# ---------------------------------------------------------------------------
# Графічний інтерфейс
# ---------------------------------------------------------------------------
C = {"edge": "#9aa3ad", "tree": "#3b82f6", "path": "#e03131", "v": "white",
     "open": "#ffe066", "closed": "#a5c8ff", "cur": "#ff922b", "start": "#40c057",
     "goal": "#fa5252", "pend": "#7048e8"}


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.apply_theme()
        self.title("ЛР №2. Пошук в глибину і в ширину на графі")
        self.geometry("1360x780")
        self.g = Graph()
        self.backup = None           # ребра до переходу в «Дерево»
        self.start_v, self.goal_v = START, GOAL
        self.vis = None              # стан підсвітки пошуку
        self.res = None
        self.step_i = 0
        self.job = None
        self.pending = None          # перша вершина для операцій з двох кліків
        self.await_parent = None     # нова вершина дерева чекає на батька
        self.runs = []
        self.res_win = None
        self.ox = 0
        self.build()
        self.redraw()

    # ---------------- інтерфейс ----------------
    def apply_theme(self):
        """Сучасний вигляд елементів: на macOS — рідна тема aqua,
        на Windows/Linux — тема Sun Valley (pip install sv-ttk), якщо встановлена."""
        if self.tk.call("tk", "windowingsystem") == "aqua":
            return
        try:
            import sv_ttk
            sv_ttk.set_theme("light")
        except ImportError:
            ttk.Style(self).theme_use("clam")

    def build(self):
        p = ttk.Frame(self, padding=6)
        p.pack(side="left", fill="y")

        f = ttk.LabelFrame(p, text="Вид графа", padding=6)
        f.pack(fill="x", pady=3)
        self.kind = tk.StringVar(value="und")
        for val, txt in (("und", "Звичайний (усі ребра)"), ("dir", "Орграф (усі дуги)"),
                         ("tree", "Дерево"), ("mix", "Змішаний: ребра і дуги разом")):
            ttk.Radiobutton(f, text=txt, value=val, variable=self.kind,
                            command=self.change_kind).pack(anchor="w")
        self.info = ttk.Label(f, justify="left")
        self.info.pack(anchor="w", pady=(4, 0))

        f = ttk.LabelFrame(p, text="Пошук", padding=6)
        f.pack(fill="x", pady=3)
        r = ttk.Frame(f)
        r.pack(fill="x", pady=(0, 4))
        ttk.Label(r, text="Метод:").pack(side="left")
        self.method = tk.StringVar(value="dfs")
        for val, txt in (("dfs", "в глибину (DFS)"), ("bfs", "в ширину (BFS)")):
            ttk.Radiobutton(r, text=txt, value=val, variable=self.method,
                            command=self.reset).pack(side="left")
        r = ttk.Frame(f)
        r.pack(fill="x")
        ttk.Label(r, text="Старт").pack(side="left")
        self.cb_s = ttk.Combobox(r, width=5, state="readonly")
        self.cb_s.pack(side="left", padx=3)
        ttk.Label(r, text="Ціль").pack(side="left")
        self.cb_g = ttk.Combobox(r, width=5, state="readonly")
        self.cb_g.pack(side="left", padx=3)
        ttk.Button(r, text="⇄", width=3, command=self.swap).pack(side="left")
        self.cb_s.bind("<<ComboboxSelected>>", self.pick_endpoints)
        self.cb_g.bind("<<ComboboxSelected>>", self.pick_endpoints)
        ttk.Label(f, text="Порядок обходу суміжних вершин:").pack(anchor="w", pady=(6, 0))
        self.cb_o = ttk.Combobox(f, state="readonly", values=list(ORDERS.values()))
        self.cb_o.current(0)
        self.cb_o.pack(fill="x")
        self.cb_o.bind("<<ComboboxSelected>>", lambda e: self.reset())
        r = ttk.Frame(f)
        r.pack(fill="x", pady=4)
        ttk.Label(r, text="Затримка, мс").pack(side="left")
        self.delay = tk.IntVar(value=400)
        ttk.Scale(r, from_=50, to=1500, variable=self.delay).pack(side="left", fill="x", expand=True)
        r = ttk.Frame(f)
        r.pack(fill="x")
        for txt, cmd in (("▶ Анімація", self.animate), ("Крок", self.step),
                         ("Миттєво", self.instant), ("Скинути", self.reset)):
            ttk.Button(r, text=txt, command=cmd).pack(side="left", fill="x", expand=True)

        f = ttk.LabelFrame(p, text="Редагування (лівий клік)", padding=6)
        f.pack(fill="x", pady=3)
        self.mode = tk.StringVar(value="link")
        for val, txt in (("addv", "Додати вершину (клік на вільному місці)"),
                         ("delv", "Видалити вершину"),
                         ("link", "З'єднати дві вершини"), ("unlink", "Видалити ребро/дугу"),
                         ("dir", "Змінити напрямок: ребро → u→v → v→u → ребро")):
            ttk.Radiobutton(f, text=txt, value=val, variable=self.mode,
                            command=self.mode_changed).pack(anchor="w")
        r = ttk.Frame(f)
        r.pack(anchor="w", pady=(4, 0))
        ttk.Label(r, text="Новий зв'язок:").pack(side="left")
        self.link_type = tk.StringVar(value="edge")
        ttk.Radiobutton(r, text="ребро", value="edge", variable=self.link_type).pack(side="left")
        ttk.Radiobutton(r, text="дуга u→v", value="arc", variable=self.link_type).pack(side="left")
        ttk.Button(f, text="Відновити заданий граф", command=self.restore).pack(fill="x", pady=(6, 0))

        ttk.Button(p, text="Вікно результатів", command=self.show_results).pack(fill="x", pady=6)

        right = ttk.Frame(self)
        right.pack(side="left", fill="both", expand=True)
        self.cv = tk.Canvas(right, bg="#fbfbf8", highlightthickness=0)
        self.cv.pack(fill="both", expand=True)
        self.cv.bind("<Button-1>", self.click)
        self.cv.bind("<Configure>", self.resized)
        self.status = tk.StringVar()
        ttk.Label(right, textvariable=self.status, relief="sunken", padding=(6, 2)).pack(fill="x")
        self.mode_changed()

    # ---------------- допоміжне ----------------
    def order(self):
        return list(ORDERS)[self.cb_o.current()]

    def resized(self, e):
        self.ox = max(0, (e.width - 900) // 2)
        self.redraw()

    def vertex_at(self, x, y):
        x -= self.ox
        for v, (vx, vy) in self.g.pos.items():
            if (vx - x) ** 2 + (vy - y) ** 2 <= (R + 3) ** 2:
                return v
        return None

    def changed(self, msg=""):
        k = self.g.kind()
        if not self.is_tree_mode():
            if k == "орграф":
                self.kind.set("dir")
            elif k == "змішаний граф":
                self.kind.set("mix")
            elif self.kind.get() != "mix":
                self.kind.set("und")
        if msg:
            self.status.set(msg)
        self.reset()

    def is_tree_mode(self):
        return self.kind.get() == "tree"

    # ---------------- вид графа ----------------
    def change_kind(self):
        k = self.kind.get()
        if k != "tree" and self.backup is not None:   # повернення ребер після дерева
            for e, d in self.backup.items():
                if e[0] in self.g.pos and e[1] in self.g.pos and not self.g.find(*e):
                    self.g.edges[e] = d
            self.backup = None
        if k == "und":
            self.g.edges = {e: False for e in self.g.edges}
        elif k == "dir":
            self.g.edges = {e: True for e in self.g.edges}
        elif k == "tree":
            self.backup = dict(self.g.edges)
            root = 1 if 1 in self.g.pos else min(self.g.pos)
            self.g = self.g.spanning_tree(root)
        if k == "dir":
            self.link_type.set("arc")
        elif k in ("und", "tree"):
            self.link_type.set("edge")
        self.status.set(f"Вид графа: {self.g.kind()}.")
        self.reset()

    # ---------------- миша ----------------
    def mode_changed(self):
        self.pending = None
        self.status.set({
            "addv": "Клацніть на вільному місці полотна — нова вершина.",
            "delv": "Клацніть по вершині — вона видалиться разом з її зв'язками.",
            "link": "Клацніть по двох вершинах (для дуги: спочатку початок, потім кінець).",
            "unlink": "Клацніть по двох кінцях зв'язку, який треба видалити.",
            "dir": "Клацніть по двох кінцях: ребро → дуга u→v → дуга v→u → ребро.",
        }[self.mode.get()])
        self.redraw()

    def add_vertex_at(self, e):
        if self.await_parent is not None:
            return
        v = self.g.add_vertex(e.x - self.ox, e.y)
        self.pending = None
        if self.is_tree_mode() and len(self.g.pos) > 1:
            self.await_parent = v
            self.status.set(f"Додано вершину {v}. Дерево: клацніть по вершині-батьку.")
            self.redraw()
            return
        self.changed(f"Додано вершину {v}.")

    def delete_vertex(self, v):
        if self.is_tree_mode() and sum(v in k for k in self.g.edges) > 1:
            messagebox.showwarning("Дерево", "З дерева можна видаляти лише листки.")
            return
        if len(self.g.pos) <= 2:
            return
        self.g.remove_vertex(v)
        if self.await_parent == v:
            self.await_parent = None
        self.changed(f"Видалено вершину {v}.")

    def click(self, e):
        v = self.vertex_at(e.x, e.y)
        m = self.mode.get()
        if v is None:
            if m == "addv":
                self.add_vertex_at(e)
            return
        if m == "delv" and self.await_parent is None:
            self.delete_vertex(v)
            return
        if self.await_parent is not None:
            if v != self.await_parent:
                self.g.edges[(v, self.await_parent)] = False
                msg = f"Вершину {self.await_parent} приєднано до {v}."
                self.await_parent = None
                self.changed(msg)
            return
        if self.pending is None or self.pending == v:
            self.pending = v
            self.status.set(f"Обрано вершину {v}, оберіть другу.")
            self.redraw()
            return
        a, b = self.pending, v
        self.pending = None
        self.edit(m, a, b)

    def edit(self, m, a, b):
        g, tree = self.g, self.is_tree_mode()
        key = g.find(a, b)
        if tree and m != "link":
            messagebox.showwarning("Дерево", "У дереві можна лише додавати ребра до нових вершин "
                                   "та видаляти листки (правий клік).")
            return self.redraw()
        if m == "link":
            arc = self.link_type.get() == "arc"
            if tree and (arc or any(a in c and b in c for c in g.components())):
                messagebox.showwarning("Дерево", "Це ребро утворить цикл (або є дугою) — "
                                       "граф перестане бути деревом.")
                return self.redraw()
            if key:
                del g.edges[key]
            g.edges[(a, b)] = arc
            return self.changed(f"Додано {'дугу ' + str(a) + '→' + str(b) if arc else 'ребро ' + str(a) + '–' + str(b)}.")
        if not key:
            self.status.set(f"Між {a} і {b} немає зв'язку.")
            return self.redraw()
        d = g.edges.pop(key)
        if m == "unlink":
            return self.changed(f"Видалено зв'язок {a}–{b}.")
        if not d:                       # ребро -> дуга a->b
            g.edges[(a, b)] = True
            msg = f"Ребро стало дугою {a}→{b}."
        elif key == (a, b):             # дуга a->b -> дуга b->a
            g.edges[(b, a)] = True
            msg = f"Дугу розвернуто: {b}→{a}."
        else:                           # дуга b->a -> ребро
            g.edges[(a, b)] = False
            msg = f"Дуга стала ребром {a}–{b}."
        self.changed(msg)

    def pick_endpoints(self, _=None):
        self.start_v, self.goal_v = int(self.cb_s.get()), int(self.cb_g.get())
        self.reset()

    def swap(self):
        self.start_v, self.goal_v = self.goal_v, self.start_v
        self.reset()

    def restore(self):
        self.g, self.backup = Graph(), None
        self.start_v, self.goal_v = START, GOAL
        self.kind.set("und")
        self.link_type.set("edge")
        self.await_parent = None
        self.reset()

    # ---------------- пошук ----------------
    def prepare(self):
        self.stop()
        if self.start_v not in self.g.pos or self.goal_v not in self.g.pos:
            messagebox.showerror("Помилка", "Задайте старт і ціль.")
            return False
        o, meth = self.order(), self.method.get()
        self.res = search(self.g, self.start_v, self.goal_v, o, meth)
        self.res.update(time=search_time_us(self.g, self.start_v, self.goal_v, o, meth), order=ORDERS[o],
                        method=METHODS[meth],
                        start=self.start_v, goal=self.goal_v, kind=self.g.kind(),
                        n=len(self.g.pos), m=len(self.g.edges))
        self.vis = {"open": {self.start_v}, "closed": set(), "cur": None, "tree": set(), "path": [], "no": {}}
        self.step_i = 0
        return True

    def apply(self, st):
        n, born, opn, closed = st
        self.vis.update(cur=n, open=set(opn), closed=set(closed))
        self.vis["no"][n] = len(closed)
        for c in born:
            self.vis["tree"].add(frozenset((c, self.res["parent"][c])))
        self.step_i += 1
        kind = "стек" if self.method.get() == "dfs" else "черга"
        self.status.set(f"Цикл {self.step_i}: розкрито {n}, породжено {born or '—'}, OPEN ({kind}) = {opn}")

    def animate(self):
        if self.prepare():
            self.redraw()
            self.job = self.after(self.delay.get(), self.tick)

    def tick(self):
        if self.step_i < len(self.res["steps"]):
            self.apply(self.res["steps"][self.step_i])
            self.redraw()
            self.job = self.after(self.delay.get(), self.tick)
        else:
            self.job = None
            self.finish()

    def step(self):
        self.stop()
        if self.vis is None or self.vis.get("done"):
            if self.prepare():
                self.status.set("Покроковий режим: натискайте «Крок».")
                self.redraw()
            return
        if self.step_i < len(self.res["steps"]):
            self.apply(self.res["steps"][self.step_i])
            self.redraw()
        else:
            self.finish()

    def instant(self):
        if self.prepare():
            for st in self.res["steps"]:
                self.apply(st)
            self.finish()

    def finish(self):
        r = self.res
        self.vis.update(cur=None, path=r["path"], done=True)
        self.runs.append(r)
        self.print_run(r)
        self.status.set(f"Шлях: {'–'.join(map(str, r['path']))} (довжина {len(r['path']) - 1}), циклів "
                        f"{r['cycles']}, розкрито {r['expanded']}" if r["path"] else
                        "Шлях не існує: список OPEN вичерпано.")
        self.redraw()
        self.show_results()

    def print_run(self, r):
        """Виводить результат запуску в консоль рядком через табуляцію (для вставки в таблицю звіту)."""
        if len(self.runs) == 1:
            print("№\tМетод\tВид графа\tn/m\tСтарт→ціль\tПорядок обходу\tШлях\tДовжина\tЦикли\tРозкриті\tЧас, мкс")
        path = "–".join(map(str, r["path"])) or "не знайдено"
        length = len(r["path"]) - 1 if r["path"] else "—"
        print(f"{len(self.runs)}\t{r['method']}\t{r['kind']}\t{r['n']}/{r['m']}\t{r['start']}→{r['goal']}\t{r['order']}\t"
              f"{path}\t{length}\t{r['cycles']}\t{r['expanded']}\t{r['time']:.1f}", flush=True)

    def stop(self):
        if self.job:
            self.after_cancel(self.job)
            self.job = None

    def reset(self):
        self.stop()
        self.vis = None
        self.redraw()

    # ---------------- малювання ----------------
    def redraw(self):
        ids = sorted(self.g.pos)
        self.cb_s["values"] = self.cb_g["values"] = ids
        if self.start_v not in self.g.pos:
            self.start_v = ids[0]
        if self.goal_v not in self.g.pos:
            self.goal_v = ids[-1]
        self.cb_s.set(self.start_v)
        self.cb_g.set(self.goal_v)
        arcs = sum(self.g.edges.values())
        self.info.config(text=f"Фактично: {self.g.kind()}\nвершин {len(self.g.pos)}, ребер "
                              f"{len(self.g.edges) - arcs}, дуг {arcs}")

        cv, g, vis, ox = self.cv, self.g, self.vis or {}, self.ox
        cv.delete("all")
        p = vis.get("path", [])
        on_path = {frozenset(e) for e in zip(p, p[1:])}
        for (u, v), d in g.edges.items():
            (x1, y1), (x2, y2) = g.pos[u], g.pos[v]
            L = math.hypot(x2 - x1, y2 - y1) or 1
            dx, dy = (x2 - x1) / L, (y2 - y1) / L
            e = frozenset((u, v))
            col, w = (C["path"], 5) if e in on_path else (C["tree"], 3) if e in vis.get("tree", ()) else (C["edge"], 2)
            cv.create_line(x1 + ox + dx * R, y1 + dy * R, x2 + ox - dx * (R + 1), y2 - dy * (R + 1),
                           fill=col, width=w, arrow="last" if d else None, arrowshape=(13, 15, 5))
        for v, (x, y) in g.pos.items():
            x += ox
            fill = C["v"]
            if v in vis.get("closed", ()):
                fill = C["closed"]
            if v in vis.get("open", ()):
                fill = C["open"]
            if v == vis.get("cur"):
                fill = C["cur"]
            if v == self.start_v:
                fill = C["start"]
            if v == self.goal_v:
                fill = C["goal"]
            ring = v in (self.pending, self.await_parent)
            cv.create_oval(x - R, y - R, x + R, y + R, fill=fill, width=4 if ring else 1.5,
                           outline=C["pend"] if ring else "#343a40")
            cv.create_text(x, y, text=v, fill="#212529", font=("DejaVu Sans", 10, "bold"))
            if v in vis.get("no", {}):
                cv.create_text(x + R, y - R, text=f"#{vis['no'][v]}", anchor="sw",
                               fill="#1c4fd6", font=("DejaVu Sans", 8))
        # легенда
        items = [("start", "старт"), ("goal", "ціль"), ("cur", "розкривається"),
                 ("open", "у списку OPEN"), ("closed", "розкрита (CLOSED)")]
        cv.create_rectangle(6, 6, 190, 20 + 20 * len(items) + 40, fill="white", outline="#ccc")
        for i, (k, t) in enumerate(items):
            y = 14 + 20 * i
            cv.create_oval(12, y, 24, y + 12, fill=C[k])
            cv.create_text(32, y + 6, text=t, anchor="w", fill="#212529", font=("DejaVu Sans", 9))
        y = 18 + 20 * len(items)
        cv.create_line(12, y, 26, y, fill=C["tree"], width=3)
        cv.create_text(32, y, text="дерево пошуку", anchor="w", fill="#212529", font=("DejaVu Sans", 9))
        cv.create_line(12, y + 20, 26, y + 20, fill=C["path"], width=5)
        cv.create_text(32, y + 20, text="шлях;  #k — № розкриття", anchor="w", fill="#212529", font=("DejaVu Sans", 9))

    # ---------------- вікно результатів ----------------
    def show_results(self):
        if not (self.res_win and self.res_win.winfo_exists()):
            w = self.res_win = tk.Toplevel(self)
            w.title("Результати пошуку")
            w.geometry("1290x430")
            self.txt = tk.Text(w, height=10, font=("DejaVu Sans Mono", 10))
            self.txt.pack(fill="x", padx=6, pady=6)
            cols = ("№", "Метод", "Вид графа", "n/m", "Старт→ціль", "Порядок обходу", "Шлях",
                    "Довжина", "Цикли", "Розкриті", "Час, мкс")
            widths = (35, 90, 130, 60, 95, 215, 300, 75, 60, 80, 80)
            self.log = ttk.Treeview(w, columns=cols, show="headings")
            for c, wd in zip(cols, widths):
                self.log.heading(c, text=c)
                self.log.column(c, width=wd, anchor="w" if c in ("Шлях", "Порядок обходу") else "center")
            self.log.pack(fill="both", expand=True, padx=6, pady=(0, 6))
            self.shown = 0
        for r in self.runs[self.shown:]:
            self.shown += 1
            self.log.insert("", "end", values=(
                self.shown, r["method"], r["kind"], f"{r['n']}/{r['m']}", f"{r['start']}→{r['goal']}", r["order"],
                "–".join(map(str, r["path"])) or "не знайдено",
                len(r["path"]) - 1 if r["path"] else "—", r["cycles"], r["expanded"], f"{r['time']:.1f}"))
        self.txt.delete("1.0", "end")
        r = self.res
        if r:
            self.txt.insert("end", "\n".join([
                f"Метод: пошук {r['method']}",
                f"Граф: {r['kind']}, вершин {r['n']}, ребер/дуг {r['m']}",
                f"Старт: {r['start']}   Ціль: {r['goal']}   Порядок обходу: {r['order']}",
                "",
                f"Знайдений шлях:            {'–'.join(map(str, r['path'])) or 'не існує'}",
                f"Довжина шляху (ребер):     {len(r['path']) - 1 if r['path'] else '—'}",
                f"Кількість циклів:          {r['cycles']}",
                f"Кількість розкритих вершин: {r['expanded']}  (породжено {r['generated']})",
                f"Час виконання пошуку:      {r['time']:.1f} мкс",
            ]))


if __name__ == "__main__":
    App().mainloop()
