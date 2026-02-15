from sim import reference

@reference(
    (0, 0, 0),
    (0, 5, 0),
    (10, 20, 0),
)
def simple(a, b, _):
    return sum(range(a, b + 1))
