void dfs(
    const int * restrict rows,
	const int * restrict cols,
	int count,
	int * stack,
	int * visited,
	int * restrict walk) {

	int stack_pos = 1;
	int walk_pos = 0;

	// Generic helpers for @stack
	#define push(val) \
	({ \
		stack[stack_pos] = val; \
		stack_pos++; \
	})

	#define pop() \
	({ \
		stack_pos--; \
		int val = stack[stack_pos]; \
		val; \
	})

	#define empty() (stack_pos == 0)

	// Walk in DFS order
	while(!empty()) {

		// Fetch the next vertex and add it to @walk
		int next = pop();
		walk[walk_pos] = next;
		walk_pos++;

		// Add unvisited neighbors to the stack
		for(int i = rows[next]; i < rows[next + 1]; i++) {
			int dst = cols[i];
			if(!visited[dst]) {
				push(dst);
				visited[dst] = 1;
			}
		}
	}
}
