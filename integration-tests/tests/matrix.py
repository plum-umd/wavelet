"""
Some helper functions for generating and manipulating matrices.
"""

import random

def random_matrix(m, n, lower=-100, upper=100):
    """Generates a random m x n matrix with values."""
    return [[random.randint(lower, upper) for _ in range(n)] for _ in range(m)]

def matrix_mul(a, b):
    """Multiplies two matrices."""
    m = len(a)
    if len(a) == 0 or len(b) == 0:
        return []
    n = len(a[0])
    p = len(b[0])
    assert len(b) == n, "incompatible matrix dimensions for multiplication"
    result = [[0 for _ in range(p)] for _ in range(m)]
    for i in range(m):
        for j in range(p):
            for k in range(n):
                result[i][j] += a[i][k] * b[k][j]
    return result
