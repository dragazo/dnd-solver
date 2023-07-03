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
    chest_pos = [(i, j) for i in range(num_rows) for j in range(num_cols) if board[i][j] == CHEST]
    assert len(chest_pos) == 1
    chest_pos = chest_pos[0]

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

    dummy_i, dummy_j, dummy_x, dummy_y = z3.Ints('dumi dumj dumx dumy')
    s.add(z3.ForAll([dummy_i, dummy_j, dummy_x, dummy_y], z3.Implies(z3.Or(dummy_i < 0, dummy_i >= num_rows, dummy_j < 0, dummy_j >= num_cols, dummy_x < 0, dummy_x >= num_rows, dummy_y < 0, dummy_y >= num_cols), z3.Not(reach(mkP(dummy_i, dummy_j), mkP(dummy_x, dummy_y))))))

    for i in range(num_rows):
        for j in range(num_cols):
            p = (i, j)
            for x in range(num_rows):
                for y in range(num_cols):
                    q = (x, y)
                    d = abs(i - x) + abs(j - y)
                    if d == 1:
                        s.add(reach(mkP(p), mkP(q)) == z3.And(sol[p] != WALL, sol[q] != WALL))
                    else:
                        s.add(z3.Not(reach(mkP(p), mkP(q))))
            s.add(z3.Or(sol[p] == WALL, reach_tc(mkP(chest_pos), mkP(p))))

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
