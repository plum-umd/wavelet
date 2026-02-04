from .. import helper

@helper.check_equiv(
    args=["a", "b"],
    init_mem={},
    tests=[
        { "a": 0, "b": 0 },
        { "a": 0, "b": 5 },
        { "a": 10, "b": 20 },
    ],
)
def simple_mem(a, b):
    return sum(range(a, b + 1))
