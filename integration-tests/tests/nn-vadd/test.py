from sim import reference

@reference(
    ([], [], [], 0),
    ([-2, 47, -52, -35, -89], [81, 11, -100, 33, 37], [0] * 5, 5),
    ([75, 84, 89, 88, 71, -50, -7, 10, -83, 70], [-16, 59, -20, 69, -69, 84, -24, 29, -21, 70], [0] * 10, 10),
)
def nn_vadd(weight, src, dest, N):
    for i in range(N):
        dest[i] = weight[i] + src[i]
