from .. import helper

@helper.check_equiv(
    args=["a", "b", "c"],
    init_mem={},
    tests=[
        { "a": 0, "b": 0, "c": 0 },
        { "a": 0, "b": 5, "c": 0 },
        { "a": 10, "b": 20, "c": 0 },
    ],
)
def simple(a, b, **_):
    return sum(range(a, b + 1))
