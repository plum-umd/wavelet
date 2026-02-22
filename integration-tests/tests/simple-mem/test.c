int simple_mem(int a, int b) {
    int res[1];
    res[0] = 0;
    for (int i = a; i <= b; i++) {
        res[0] += i;
    }
    return res[0];
}
