from sim import reference

@reference(
    (0, 0),
    (0, 5),
    (10, 20),
)
def simple_mem(a, b):
    return sum(range(a, b + 1))
