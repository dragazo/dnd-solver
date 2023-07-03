import sys
import z3

HALL = 0
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
    HALL: '  ',
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
            s.add(z3.Or(v == HALL, v == ROOM, v == WALL))
        else:
            s.add(v == val)
        return v

    # create all the tiles - pad the borders with out-of-bounds walls
    sol = { (i, j): make_state(f'v{i},{j}', board[i][j]) for j in range(num_cols) for i in range(num_rows) }
    for i in range(num_rows):
        sol[(i, -1)] = sol[(i, num_cols)] = WALL
    for j in range(num_cols):
        sol[(-1, j)] = sol[(num_rows, j)] = WALL
    assert len(sol) == (num_rows + 2) * (num_cols + 2) - 4

    # make sure we satisfy the hints for number of walls in rows/cols
    for i in range(num_rows):
        s.add(sum(z3.If(sol[(i, j)] == WALL, 1, 0) for j in range(num_cols)) == row_hints[i])
    for j in range(num_cols):
        s.add(sum(z3.If(sol[(i, j)] == WALL, 1, 0) for i in range(num_rows)) == col_hints[j])

    # all non-walls must form a single connected component (connected from a single arbitrary known non-wall)
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

    # dead end (degree 1) iff monster
    for i in range(num_rows):
        for j in range(num_cols):
            p = (i, j)
            adj = [(i - 1, j), (i, j - 1), (i, j + 1), (i + 1, j)]
            deg = sum(z3.If(sol[q] != WALL, 1, 0) for q in adj)
            s.add(z3.Implies(sol[p] != WALL, (deg == 1) == (sol[p] == MONSTER)))

    # no 2x2 hallway subgraphs
    for i in range(1, num_rows):
        for j in range(1, num_cols):
            group = [(i - 1, j - 1), (i - 1, j), (i, j - 1), (i, j)]
            s.add(z3.Implies(z3.And(*[sol[p] != WALL for p in group]), z3.And(*[sol[p] != HALL for p in group])))

    # treasure rooms
    for chest in chest_pos:
        interiors = [(-1, -1), (-1, 0), (-1, 1), (0, -1), (0, 0), (0, 1), (1, -1), (1, 0), (1, 1)]
        borders = [(-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, 2), (0, -2), (0, 2), (1, -2), (1, 2), (2, -1), (2, 0), (2, 1)]
        options = []
        for delta in interiors:
            center = (chest[0] + delta[0], chest[1] + delta[1])
            if center[0] < 1 or center[0] >= num_rows - 1 or center[1] < 1 or center[1] >= num_cols - 1:
                continue
            is_3x3 = z3.And(*[sol[(center[0] + dx, center[1] + dy)] != WALL for dx, dy in interiors])
            is_enclosed = sum(z3.If(sol[(center[0] + dx, center[1] + dy)] == WALL, 1, 0) for dx, dy in borders) == 11
            options.append(z3.And(is_3x3, is_enclosed))
        s.add(z3.Or(*options))

    # decide room/hall for empty spaces
    s.add(sum(z3.If(sol[(i, j)] == ROOM, 1, 0) for i in range(num_rows) for j in range(num_cols)) == 8 * len(chest_pos))

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
