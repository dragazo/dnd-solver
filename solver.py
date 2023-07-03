import sys
import z3

SPACE = 0
ROOM = 1
WALL = 2
CHEST = 3
MONSTER = 4

PARSER = {
    '.': None,
    'w': WALL,
    'c': CHEST,
    'm': MONSTER,
}
DISPLAY = {
    SPACE: '  ',
    ROOM: '⭐',
    WALL: '🧱',
    CHEST: '🏆',
    MONSTER: '👿',
}

def main():
    with open(sys.argv[1], 'r') as f:
        content = f.read()
    print(f'input:\n\n{content}\n')

    board = [x.split() for x in content.splitlines()]
    for row in board[1:]:
        assert len(row) == len(board[0]) + 1
    col_hints = [int(x) for x in board[0]]
    row_hints = [int(x[0]) for x in board[1:]]
    board = [[PARSER[y] for y in x[1:]] for x in board[1:]]
    num_cols = len(col_hints)
    num_rows = len(row_hints)
    knowns = [(i, j) for i in range(num_rows) for j in range(num_cols) if board[i][j] is not None and board[i][j] != WALL]
    chest_pos = [(i, j) for i in range(num_rows) for j in range(num_cols) if board[i][j] == CHEST]
    assert len(knowns) >= 1

    s = z3.Solver()
    def make_state(name, val):
        v = z3.Int(name)
        if val is None:
            s.add(z3.Or(v == SPACE, v == ROOM, v == WALL))
        else:
            s.add(v == val)
        return v
    sol = { (i, j): make_state(f'v{i},{j}', board[i][j]) for j in range(num_cols) for i in range(num_rows) }
    for i in range(num_rows):
        sol[(i, -1)] = sol[(i, num_cols)] = WALL
    for j in range(num_cols):
        sol[(-1, j)] = sol[(num_rows, j)] = WALL
    assert len(sol) == (num_rows + 2) * (num_cols + 2) - 4

    for i in range(num_rows):
        s.add(sum(z3.If(sol[(i, j)] == WALL, 1, 0) for j in range(num_cols)) == row_hints[i])
    for j in range(num_cols):
        s.add(sum(z3.If(sol[(i, j)] == WALL, 1, 0) for i in range(num_rows)) == col_hints[j])

    P, mkP, _ = z3.TupleSort('P', [z3.IntSort(), z3.IntSort()])
    reach = z3.Function('r', P, P, z3.BoolSort())
    reach_tc = z3.TransitiveClosure(reach)

    dum = z3.Ints('dumi dumj dumx dumy')
    out_of_bounds = z3.Or(dum[0] < 0, dum[0] >= num_rows, dum[1] < 0, dum[1] >= num_cols, dum[2] < 0, dum[2] >= num_rows, dum[3] < 0, dum[3] >= num_cols)
    s.add(z3.ForAll(dum, z3.Implies(out_of_bounds, z3.Not(reach(mkP(dum[0], dum[1]), mkP(dum[2], dum[3]))))))

    for i in range(num_rows):
        for j in range(num_cols):
            p = (i, j)
            for x in range(num_rows):
                for y in range(num_cols):
                    q = (x, y)
                    d = abs(i - x) + abs(j - y)
                    if d == 0:
                        s.add(reach(mkP(p), mkP(q)))
                    elif d == 1:
                        s.add(reach(mkP(p), mkP(q)) == z3.And(sol[p] != WALL, sol[q] != WALL))
                    else:
                        s.add(z3.Not(reach(mkP(p), mkP(q))))
            s.add(z3.Or(sol[p] == WALL, reach_tc(mkP(knowns[0]), mkP(p))))

    deg = {}
    for i in range(num_rows):
        for j in range(num_cols):
            p = (i, j)
            adj = [(i - 1, j), (i, j - 1), (i, j + 1), (i + 1, j)]
            deg[p] = sum(z3.If(sol[q] != WALL, 1, 0) for q in adj)
            s.add(z3.Implies(sol[p] != WALL, (deg[p] == 1) == (sol[p] == MONSTER)))

    res = s.check()
    if res == z3.sat:
        print('solution:\n')
        m = s.model()
        for i in range(num_rows):
            for j in range(num_cols):
                v = m.eval(sol[(i, j)]).as_long()
                print(DISPLAY[v], end = '')
            print()
    else:
        print('no solution!')

main()
