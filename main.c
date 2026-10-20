#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
 
#define V        50
#define SPARSE_E 100
#define DENSE_E  600
#define INF      1000000
#define REPEAT   20000      
 
typedef struct { int u, v, w; } Edge;
 
typedef struct Node {
    int v, w;
    struct Node *next;
} Node;
 
typedef struct {
    int  e;                 
    Edge edges[DENSE_E];    
    Node *head[V];         
    int  mat[V][V];        
} Graph;
 
static Graph sparse, dense;
 
static void add_edge(Graph *g, int u, int v)
{
    int w = rand() % 100 + 1;
 
    g->mat[u][v] = g->mat[v][u] = w;
    g->edges[g->e].u = u;
    g->edges[g->e].v = v;
    g->edges[g->e].w = w;
    g->e++;
}
 
static void dfs(Graph *g, int u, int *seen)
{
    seen[u] = 1;
    for (int v = 0; v < V; v++)
        if (g->mat[u][v] && !seen[v])
            dfs(g, v, seen);
}
 
static int is_connected(Graph *g)
{
    int seen[V] = {0};
 
    dfs(g, 0, seen);
    for (int i = 0; i < V; i++)
        if (!seen[i]) return 0;
    return 1;
}
 
static void push_node(Graph *g, int u, int v, int w)
{
    Node *n = malloc(sizeof(Node));
 
    n->v = v;
    n->w = w;
    n->next = g->head[u];
    g->head[u] = n;
}
 
static void make_graph(Graph *g, int e_cnt)
{
    do {
        memset(g, 0, sizeof(Graph));
 
     
        for (int i = 1; i < V; i++)
            add_edge(g, i, rand() % i);
 
        /* 나머지 간선은 랜덤으로 */
        while (g->e < e_cnt) {
            int u = rand() % V;
            int v = rand() % V;
 
            if (u == v || g->mat[u][v]) continue;
            add_edge(g, u, v);
        }
    } while (!is_connected(g));   
 
    /* 같은 간선으로 인접 리스트도 만든다 */
    for (int i = 0; i < g->e; i++) {
        push_node(g, g->edges[i].u, g->edges[i].v, g->edges[i].w);
        push_node(g, g->edges[i].v, g->edges[i].u, g->edges[i].w);
    }
}
 

 
static Edge kedges[DENSE_E];    /* 리스트에서 꺼낸 간선 */
static Edge kmst[V - 1];        /* 결과 */
static int  parent[V], rnk[V];  /* union-find */
 
static int cmp_edge(const void *a, const void *b)
{
    return ((const Edge *)a)->w - ((const Edge *)b)->w;
}
 
static int find(int x)
{
    while (parent[x] != x) {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    return x;
}
 
static int kruskal(Graph *g, long *cost)
{
    int m = 0, cnt = 0;
    long total = 0;
 

    for (int u = 0; u < V; u++)
        for (Node *p = g->head[u]; p; p = p->next)
            if (u < p->v) {
                kedges[m].u = u;
                kedges[m].v = p->v;
                kedges[m].w = p->w;
                m++;
            }
 
    qsort(kedges, m, sizeof(Edge), cmp_edge);
 
    for (int i = 0; i < V; i++) {
        parent[i] = i;
        rnk[i] = 0;
    }
 
    for (int i = 0; i < m && cnt < V - 1; i++) {
        int a = find(kedges[i].u);
        int b = find(kedges[i].v);
 
        if (a == b) continue;     
 
        if (rnk[a] < rnk[b]) { int t = a; a = b; b = t; }
        parent[b] = a;
        if (rnk[a] == rnk[b]) rnk[a]++;
 
        kmst[cnt++] = kedges[i];
        total += kedges[i].w;
    }
 
    *cost = total;
    return cnt;
}
 
static size_t kruskal_memory(Graph *g)
{
    return sizeof(g->head) + (size_t)(2 * g->e) * sizeof(Node)   
         + (size_t)g->e * sizeof(Edge)                          
         + sizeof(parent) + sizeof(rnk)                      
         + sizeof(kmst);                                      
}

 
static int key[V], pre[V], in_mst[V];
 
static int prim(Graph *g, long *cost)
{
    long total = 0;
    int cnt = 0;
 
    for (int i = 0; i < V; i++) {
        key[i] = INF;
        pre[i] = -1;
        in_mst[i] = 0;
    }
    key[0] = 0;
 
    for (int k = 0; k < V; k++) {
        int u = -1;
 
        for (int i = 0; i < V; i++)
            if (!in_mst[i] && (u == -1 || key[i] < key[u]))
                u = i;
 
        in_mst[u] = 1;
        total += key[u];
        if (pre[u] != -1) cnt++;
 
        for (int v = 0; v < V; v++)
            if (g->mat[u][v] && !in_mst[v] && g->mat[u][v] < key[v]) {
                key[v] = g->mat[u][v];
                pre[v] = u;
            }
    }
 
    *cost = total;
    return cnt;
}
 
static size_t prim_memory(Graph *g)
{
    return sizeof(g->mat) + sizeof(key) + sizeof(pre) + sizeof(in_mst);
}
 
 
static long cost_k[2], cost_p[2];  
 
static void print_header(int no, const char *gname, const char *rep, const char *algo, Graph *g)
{
    printf("Case %d : %s Graph - %s - %s\n", no, gname, rep, algo);
    printf("Vertices      : %d\n", V);
    printf("Edges         : %d\n", g->e);
}
 
static void run_kruskal(int no, const char *gname, Graph *g, int idx)
{
    long cost = 0;
    int cnt = 0;
 
    clock_t s = clock();
    for (int i = 0; i < REPEAT; i++)
        cnt = kruskal(g, &cost);
    clock_t t = clock();
    double us = (double)(t - s) / CLOCKS_PER_SEC * 1e6 / REPEAT;
 
    print_header(no, gname, "Adjacency List", "Kruskal", g);
    printf("MST Edges     : %d\n", cnt);
    printf("MST Cost      : %ld\n", cost);
    printf("Memory        : %zu Bytes\n", kruskal_memory(g));
    printf("Execution Time: %.3f us\n", us);
 
    printf("MST edges (u, v, w):\n");
    for (int i = 0; i < cnt; i++)
        printf("  (%d, %d) %d%s", kmst[i].u, kmst[i].v, kmst[i].w, (i % 5 == 4) ? "\n" : "");
    printf("\n\n");
 
    cost_k[idx] = cost;
}
 
static void run_prim(int no, const char *gname, Graph *g, int idx)
{
    long cost = 0;
    int cnt = 0;
 
    clock_t s = clock();
    for (int i = 0; i < REPEAT; i++)
        cnt = prim(g, &cost);
    clock_t t = clock();
    double us = (double)(t - s) / CLOCKS_PER_SEC * 1e6 / REPEAT;
 
    print_header(no, gname, "Adjacency Matrix", "Prim", g);
    printf("MST Edges     : %d\n", cnt);
    printf("MST Cost      : %ld\n", cost);
    printf("Memory        : %zu Bytes\n", prim_memory(g));
    printf("Execution Time: %.3f us\n", us);
 
    printf("MST edges (u, v, w):\n");
    int n = 0;
    for (int v = 0; v < V; v++) {
        if (pre[v] == -1) continue;
        printf("  (%d, %d) %d%s", pre[v], v, g->mat[pre[v]][v], (n % 5 == 4) ? "\n" : "");
        n++;
    }
    printf("\n\n");
 
    cost_p[idx] = cost;
}
 
int main(int argc, char *argv[])
{
    unsigned seed = (argc > 1) ? (unsigned)atoi(argv[1]) : 1234;
 
    srand(seed);
    make_graph(&sparse, SPARSE_E);
    make_graph(&dense, DENSE_E);
 
    printf("seed = %u, 실행시간은 %d번 반복한 평균 (단위: us)\n\n", seed, REPEAT);
 
    run_kruskal(1, "Sparse", &sparse, 0);
    run_kruskal(2, "Dense",  &dense,  1);
    run_prim(3, "Sparse", &sparse, 0);
    run_prim(4, "Dense",  &dense,  1);
 
    printf("Sparse : Kruskal %ld / Prim %ld -> %s\n", cost_k[0], cost_p[0], cost_k[0] == cost_p[0] ? "same" : "DIFFERENT");
    printf("Dense  : Kruskal %ld / Prim %ld -> %s\n", cost_k[1], cost_p[1], cost_k[1] == cost_p[1] ? "same" : "DIFFERENT");
 
    return 0;
}
