void bfs(
	const int * restrict rows,
	const int * restrict cols,
	int count,
	int * queue,
	int * visited,
	int * restrict walk
)
{

	int queue_front = 0;
	int queue_back = 1;
	int walk_pos = 0;

	// Generic helpers for @queue
	#define push(val) \
	({ \
		queue[queue_back] = val; \
		queue_back++; \
	})

	#define pop() \
	({ \
		int val = queue[queue_front]; \
		queue_front++; \
		val; \
	})

	#define empty() (queue_front == queue_back)

	// Walk in BFS order
	while(!empty()) {

		// Fetch the next vertex and add it to @walk
		int next = pop();
		walk[walk_pos] = next;
		walk_pos++;

		// Add unvisited neighbors to the queue
		for(int i = rows[next] ; i < rows[next + 1]; i++) {
			int dst = cols[i];
			if(!visited[dst]) {
				push(dst);
				visited[dst] = 1;
			}
		}
	}
}
