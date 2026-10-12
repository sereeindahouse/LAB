import itertools

import networkx as nx
import matplotlib.pyplot as plt


def is_valid_coloring(graph, coloring):
    return (
        coloring is not None
        and all(node in coloring for node in graph.nodes)
        and all(coloring[u] != coloring[v] for u, v in graph.edges)
    )


def _check_graph(graph):
    if graph.is_directed():
        raise ValueError("Use an undirected graph for vertex coloring")
    if nx.number_of_selfloops(graph):
        raise ValueError("A graph with a self-loop cannot be properly colored")

def greedy_coloring(graph, use_degree=False):
    _check_graph(graph)
    coloring = {}
    nodes = list(graph.nodes)
    if use_degree:
        nodes.sort(key=lambda node: graph.degree(node), reverse=True)
    for node in nodes:
        adjacent_colors = {
            coloring[neighbor]
            for neighbor in graph.neighbors(node)
            if neighbor in coloring
        }
        coloring[node] = next(color for color in itertools.count() if color not in adjacent_colors)
    return coloring


def mrv_coloring(graph, num_colors):
    _check_graph(graph)
    if not isinstance(num_colors, int) or isinstance(num_colors, bool) or num_colors < 0:
        raise ValueError("num_colors must be a nonnegative integer")

    coloring = {}
    domains = {node: set(range(num_colors)) for node in graph.nodes}

    def backtrack(remaining_domains):
        if not remaining_domains:
            return True
        node = min(
            remaining_domains,
            key=lambda candidate: (
                len(remaining_domains[candidate]),
                -sum(neighbor in remaining_domains for neighbor in graph.neighbors(candidate)),
            ),
        )
        for color in sorted(remaining_domains[node]):
            next_domains = {
                other: values - {color} if graph.has_edge(node, other) else values.copy()
                for other, values in remaining_domains.items()
                if other != node
            }
            if any(not values for values in next_domains.values()):
                continue
            coloring[node] = color
            if backtrack(next_domains):
                return True
            del coloring[node]
        return False

    return coloring if backtrack(domains) else None


def main():
    n_nodes = 25
    num_colors = 3
    graph = nx.gnp_random_graph(n_nodes, 0.1, seed=42)
    results = [
        ("Greedy", greedy_coloring(graph)),
        ("Greedy + degree", greedy_coloring(graph, use_degree=True)),
        (f"MRV + degree (limit={num_colors})", mrv_coloring(graph, num_colors)),
    ]

    positions = nx.spring_layout(graph, seed=42)
    figure, axes = plt.subplots(1, len(results), figsize=(15, 5))
    max_colors = max(
        (len(set(coloring.values())) for _, coloring in results if coloring is not None),
        default=1,
    )
    for axis, (name, coloring) in zip(axes, results):
        print(f"\n{name}")
        if coloring is None:
            print(f"No coloring exists using at most {num_colors} colors.")
            node_colors = "lightgray"
            title = f"{name}\nNo solution"
        else:
            used_colors = len(set(coloring.values()))
            print("Coloring:", coloring)
            print("Valid:", is_valid_coloring(graph, coloring))
            print("K:", used_colors)
            print("Vertex order:", list(coloring))
            node_colors = [coloring[node] for node in graph.nodes]
            title = f"{name}\nK={used_colors}"
        nx.draw(
            graph, pos=positions, node_color=node_colors, with_labels=True,
            font_weight="bold", cmap=plt.cm.tab10, vmin=0,
            vmax=max(1, max_colors - 1), ax=axis,
        )
        axis.set_title(title)
    figure.tight_layout()
    plt.show()


if __name__ == "__main__":
    main()
