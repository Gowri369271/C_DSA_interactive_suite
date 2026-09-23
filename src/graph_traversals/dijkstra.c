#include "advanced_heaps.h"
#include "graph_traversals.h"
#include "safe_input.h"
#include "step_debugger.h"
#include "telemetry.h"
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

// Min-heap ordering for PQ_graph: a node has higher priority when its
// "distance" (used as a generic priority: g+h for A*, h for Greedy, path
// cost for Dijkstra) is smaller. Equal priorities are broken by the lower
// vertex id so expansion order is deterministic and platform-independent.
static int pq_graph_higher_priority(PQ_graph_node a, PQ_graph_node b)
{
    if (a.distance != b.distance)
        return a.distance < b.distance;
    return a.vertex < b.vertex;
}

void init_pq_graph(PQ_graph* pq, int initial_capacity)
{
    if (pq == NULL)
        return;
    pq->size = 0;
    pq->capacity = initial_capacity > 0 ? initial_capacity : 10;
    pq->heap = malloc(pq->capacity * sizeof(PQ_graph_node));
    if (pq->heap == NULL)
    {
        pq->capacity = 0;
        return;
    }
}

void PQ_Destroy(PQ_graph* pq)
{
    if (pq == NULL)
        return;
    if (pq->heap != NULL)
    {
        free(pq->heap);
        pq->heap = NULL;
    }
    pq->size = 0;
    pq->capacity = 0;
}

void free_pq_graph(PQ_graph* pq)
{
    PQ_Destroy(pq);
}

int insert_pq_graph(PQ_graph* pq, int vertex, int distance)
{
    if (pq == NULL || pq->heap == NULL)
        return 0;

    if (pq->size == pq->capacity)
    {
        int new_capacity = pq->capacity * 2;
        PQ_graph_node* new_heap = realloc(pq->heap, new_capacity * sizeof(PQ_graph_node));
        if (new_heap == NULL)
            return 0;
        pq->heap = new_heap;
        pq->capacity = new_capacity;
    }

    int i = pq->size;
    pq->heap[i].distance = distance;
    pq->heap[i].vertex = vertex;
    pq->size++;

    while (i > 0)
    {
        int parent = (i - 1) / 2;
        if (!pq_graph_higher_priority(pq->heap[i], pq->heap[parent]))
            break;

        PQ_graph_node temp = pq->heap[i];
        pq->heap[i] = pq->heap[parent];
        pq->heap[parent] = temp;

        i = parent;
    }

    return 1;
}

bool extractTop_pq_graph(PQ_graph* pq, PQ_graph_node* result)
{
    if (pq == NULL || result == NULL || pq->size == 0 || pq->heap == NULL)
        return false;

    int topIndex = 0;
    PQ_graph_node topElement = pq->heap[topIndex];
    int lastElementIndex = pq->size - 1;

    pq->heap[topIndex] = pq->heap[lastElementIndex];
    pq->size--;

    int i = 0;

    while (1)
    {
        int left = 2 * i + 1;
        int right = 2 * i + 2;
        int target = i;

        if (left < pq->size && pq_graph_higher_priority(pq->heap[left], pq->heap[target]))
            target = left;
        if (right < pq->size && pq_graph_higher_priority(pq->heap[right], pq->heap[target]))
            target = right;

        if (target == i)
            break;

        PQ_graph_node temp = pq->heap[i];
        pq->heap[i] = pq->heap[target];
        pq->heap[target] = temp;

        i = target;
    }

    *result = topElement;

    return true;
}

// note: the time measured by clock() covers the shortest-path computation only
// (it stops before the distance table is printed). it is for demonstration only
// and must not be treated as a measure of the algorithm's efficiency.
void dijkstra(weightedGraph* graph, int start)
{
    telemetry_init("dijkstra");
    if (graph == NULL || start < 0 || start >= graph->V)
    {
        printf("\nError: invalid graph or starting node passed to Dijkstra");
        telemetry_close();
        return;
    }
    int size = graph->V;
    int dist[size];

    for (int i = 0; i < size; i++)
        dist[i] = INT_MAX;

    dist[start] = 0;

    clock_t start_t, end_t;
    double total_t = 0.0;

    start_t = clock();

        PQ_graph pq = {0};
        init_pq_graph(&pq, 10);
        telemetry_bridge_reset("Dijkstra (Binary)");

        if (!insert_pq_graph(&pq, start, 0))
        {
            printf("Malloc failed\n");
            PQ_Destroy(&pq);
            return;
        }

        PQ_graph_node currentNode;
        int step_counter = 1;

        while (extractTop_pq_graph(&pq, &currentNode))
        {
            int u = currentNode.vertex;

            if (currentNode.distance > dist[u])
                continue;

            char msg[128];
            snprintf(msg, sizeof(msg), "Dijkstra (Binary): Extracted node %d (distance %d)", u,
                     dist[u]);

            // Update Telemetry Bridge on extraction
            AlgorithmStateBridge bridge = {0};
            telemetry_bridge_get(&bridge);
            strncpy(bridge.algorithm_name, "Dijkstra (Binary)", sizeof(bridge.algorithm_name) - 1);
            bridge.step_index = step_counter++;
            bridge.var_count = 2;
            strncpy(bridge.variables[0].name, "curr_vertex", 31);
            snprintf(bridge.variables[0].value, 63, "%d", u);
            strncpy(bridge.variables[1].name, "curr_dist", 31);
            snprintf(bridge.variables[1].value, 63, "%d", dist[u]);
            strncpy(bridge.status_message, msg, sizeof(bridge.status_message) - 1);
            telemetry_bridge_update(&bridge);

            algorithm_step_hook(msg);

            Edge* current = graph->array[u];

            while (current != NULL)
            {
                int v = current->destination;
                int currentWeight = current->weight;
                if (dist[u] != INT_MAX && dist[u] + currentWeight < dist[v])
                {
                    dist[v] = dist[u] + currentWeight;
                    snprintf(msg, sizeof(msg),
                             "Dijkstra (Binary): Relaxed edge %d -> %d (new dist %d)", u, v,
                             dist[v]);

                    // Update Telemetry Bridge on relaxation
                    bridge.step_index = step_counter++;
                    strncpy(bridge.status_message, msg, sizeof(bridge.status_message) - 1);
                    telemetry_bridge_update(&bridge);

                    algorithm_step_hook(msg);
                    if (!insert_pq_graph(&pq, v, dist[v]))
                    {
                        printf("Malloc Failed\n");
                        PQ_Destroy(&pq);
                        return;
                    }
                }

                current = current->next;
            }
        }
        PQ_Destroy(&pq);

    end_t = clock();
    total_t = (double)(end_t - start_t) / CLOCKS_PER_SEC;

    printf("Start -> Vertex  \t  Distance\n");
    printf("---------------  \t  --------\n");

    for (int i = 0; i < size; i++)
    {
        if (dist[i] == INT_MAX)
            printf("    %d -> %d  \t            INF   \n", start, i);
        else
            printf("    %d -> %d  \t             %d   \n", start, i, dist[i]);
    }

    printf("\ntotal CPU time taken for Dijkstra's algorithm:- %f seconds\n", total_t);
    telemetry_close();
}

weightedGraph* create_weightedGraph(int V)
{
    weightedGraph* graph = malloc(sizeof(weightedGraph));

    if (!graph)
        return NULL;

    graph->V = V;

    graph->array = malloc(V * sizeof(Edge*));

    if (!graph->array)
    {
        free(graph);
        return NULL;
    }

    for (int i = 0; i < V; i++)
        graph->array[i] = NULL;

    return graph;
}

int edge_insertAtEnd(Edge** head, int dest, int weight)
{
    Edge* edge = malloc(sizeof(Edge));

    if (!edge)
        return -1;

    edge->destination = dest;
    edge->weight = weight;
    edge->next = NULL;

    if (*head == NULL)
    {
        *head = edge;
        return 1;
    }

    Edge* temp = *head;

    while (temp->next != NULL)
        temp = temp->next;

    temp->next = edge;
    return 1;
}

void add_edge_directed(weightedGraph* graph, int src, int dest, int wt)
{
    if (!graph)
        return;

    if (src < 0 || src >= graph->V || dest < 0 || dest >= graph->V)
    {
        printf("Invalid edge: %d -> %d with weight %d\n", src, dest, wt);
        return;
    }

    edge_insertAtEnd(&graph->array[src], dest, wt);
}

void free_weightedGraph(weightedGraph* graph)
{
    if (!graph)
        return;

    for (int i = 0; i < graph->V; i++)
    {
        Edge* temp = graph->array[i];
        while (temp != NULL)
        {
            Edge* prev = temp;
            temp = temp->next;
            free(prev);
        }
    }

    free(graph->array);
    free(graph);
}
