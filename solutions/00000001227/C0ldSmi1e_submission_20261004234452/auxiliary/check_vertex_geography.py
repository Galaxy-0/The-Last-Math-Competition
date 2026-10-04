#!/usr/bin/env python3
"""Finite sanity check for conjecture 00000001227; this is not a proof.

Run with Python 3 and its standard library only:
    python3 check_vertex_geography.py --max-n 6 --json results.json

For every n in 0..max_n, enumerate every labelled simple undirected graph on
vertices 0..n-1, and every start vertex. The token starts on a visited vertex.
Players alternate moving along an edge to an unvisited vertex; no legal move
means the player whose turn it is loses (normal play).

One recursion directly enumerates all matchings as tuples of edges. From these
we find maximum CARDINALITY and the vertices saturated by every such matching.
A separate recursion evaluates the game solely from adjacency, current vertex,
and the visited set; it does not consult any matching computation.

All disconnected graphs and isolated starts are included. For n=0 there is one
empty graph, one empty matching, and no start positions to compare. The source's
mention of perfect matchings is not used to restrict the quantified maximum
matchings. This check tests only the explicitly stated iff criterion under the
finite/simple/undirected/normal-play interpretation above, not historical claims.
"""

import argparse
from datetime import datetime, timezone
from functools import lru_cache
from itertools import combinations
import json
import platform
import sys
import time


def enumerate_matchings(adjacency, available):
    """Yield each matching once, including the empty matching.

    Remove the least available vertex, either leaving it unmatched or pairing
    it with each available neighbor in turn. The yielded object records the
    actual matching edges, not just its cardinality or saturation set.
    """
    if available == 0:
        yield ()
        return
    vertex_bit = available & -available
    vertex = vertex_bit.bit_length() - 1
    rest = available ^ vertex_bit
    yield from enumerate_matchings(adjacency, rest)
    possible_partners = adjacency[vertex] & rest
    while possible_partners:
        partner_bit = possible_partners & -possible_partners
        possible_partners ^= partner_bit
        partner = partner_bit.bit_length() - 1
        for smaller in enumerate_matchings(adjacency, rest ^ partner_bit):
            yield ((vertex, partner),) + smaller


def matching_summary(adjacency):
    all_vertices = (1 << len(adjacency)) - 1
    maximum_size = -1
    mandatory_vertices = all_vertices
    matching_count = 0
    maximum_matching_count = 0
    for matching in enumerate_matchings(adjacency, all_vertices):
        matching_count += 1
        size = len(matching)
        saturated = 0
        for u, v in matching:
            assert adjacency[u] & (1 << v)
            assert not (saturated & ((1 << u) | (1 << v)))
            saturated |= (1 << u) | (1 << v)
        if size > maximum_size:
            maximum_size = size
            maximum_matching_count = 1
            mandatory_vertices = saturated
        elif size == maximum_size:
            maximum_matching_count += 1
            mandatory_vertices &= saturated
    assert matching_count >= 1 and maximum_matching_count >= 1
    return maximum_size, mandatory_vertices, matching_count, maximum_matching_count


def game_evaluator(adjacency):
    @lru_cache(maxsize=None)
    def current_player_wins(current, visited):
        assert visited & (1 << current)
        legal_destinations = adjacency[current] & ~visited
        while legal_destinations:
            next_bit = legal_destinations & -legal_destinations
            legal_destinations ^= next_bit
            destination = next_bit.bit_length() - 1
            if not current_player_wins(destination, visited | next_bit):
                return True
        return False

    return current_player_wins


def is_connected(adjacency):
    # Empty graph reported separately, not assigned a connectivity convention.
    if not adjacency:
        return None
    reached = 1
    pending = 1
    while pending:
        vertex_bit = pending & -pending
        pending ^= vertex_bit
        vertex = vertex_bit.bit_length() - 1
        newly_reached = adjacency[vertex] & ~reached
        reached |= newly_reached
        pending |= newly_reached
    return reached == (1 << len(adjacency)) - 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-n", type=int, default=6)
    parser.add_argument("--json", type=str)
    args = parser.parse_args()
    if args.max_n < 0:
        parser.error("--max-n must be nonnegative")

    started = time.perf_counter()
    report = {
        "conjecture": "00000001227",
        "scope": "All labelled finite simple undirected graphs, normal-play vertex geography",
        "criterion": "First player wins iff every maximum-cardinality matching saturates start",
        "warning": "Finite sanity evidence only; not a substitute for a general proof",
        "max_n": args.max_n,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "python": sys.version,
        "platform": platform.platform(),
        "per_n": [],
        "failures": [],
    }
    print(report["warning"], flush=True)
    print(report["scope"], flush=True)
    print(report["criterion"], flush=True)
    print("n=0: one empty graph and one empty matching; no start positions.", flush=True)
    print("n graphs starts wins losses disconnected_graphs isolated_starts matchings maximum_matchings game_states failures elapsed_seconds", flush=True)
    for n in range(args.max_n + 1):
        per_n_started = time.perf_counter()
        edges = tuple(combinations(range(n), 2))
        row = dict.fromkeys(("n", "graphs", "starts", "wins", "losses", "disconnected_graphs", "isolated_starts", "matchings", "maximum_matchings", "game_states", "failures"), 0)
        row["n"] = n
        for edge_mask in range(1 << len(edges)):
            adjacency = [0] * n
            for edge_index, (u, v) in enumerate(edges):
                if edge_mask & (1 << edge_index):
                    adjacency[u] |= 1 << v
                    adjacency[v] |= 1 << u
            adjacency = tuple(adjacency)
            row["graphs"] += 1
            row["disconnected_graphs"] += is_connected(adjacency) is False
            maximum_size, mandatory, matching_count, maximum_count = matching_summary(adjacency)
            row["matchings"] += matching_count
            row["maximum_matchings"] += maximum_count
            game = game_evaluator(adjacency)
            for start in range(n):
                game_wins = game(start, 1 << start)
                matching_predicts_win = bool(mandatory & (1 << start))
                row["starts"] += 1
                row["wins"] += game_wins
                row["losses"] += not game_wins
                row["isolated_starts"] += adjacency[start] == 0
                if game_wins != matching_predicts_win:
                    row["failures"] += 1
                    report["failures"].append({
                        "n": n, "edge_mask": edge_mask, "start": start,
                        "edges": [edge for i, edge in enumerate(edges) if edge_mask & (1 << i)],
                        "game_wins": game_wins,
                        "matching_predicts_win": matching_predicts_win,
                        "maximum_matching_size": maximum_size,
                    })
            row["game_states"] += game.cache_info().currsize
        assert row["graphs"] == 1 << (n * (n - 1) // 2)
        assert row["starts"] == n * row["graphs"]
        assert row["wins"] + row["losses"] == row["starts"]
        assert row["isolated_starts"] == (n * (1 << ((n - 1) * (n - 2) // 2)) if n else 0)
        row["elapsed_seconds"] = time.perf_counter() - per_n_started
        report["per_n"].append(row)
        print(" ".join(str(row[key]) for key in ("n", "graphs", "starts", "wins", "losses", "disconnected_graphs", "isolated_starts", "matchings", "maximum_matchings", "game_states", "failures")) + f" {row['elapsed_seconds']:.6f}", flush=True)

    report["totals"] = {
        key: sum(row[key] for row in report["per_n"])
        for key in ("graphs", "starts", "wins", "losses", "disconnected_graphs", "isolated_starts", "matchings", "maximum_matchings", "game_states", "failures")
    }
    report["elapsed_seconds"] = time.perf_counter() - started
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    print("TOTAL " + json.dumps(report["totals"], sort_keys=True), flush=True)
    print(f"Elapsed wall seconds: {report['elapsed_seconds']:.6f}", flush=True)
    if args.json:
        with open(args.json, "w", encoding="utf-8") as handle:
            json.dump(report, handle, indent=2)
            handle.write("\n")
    assert report["totals"]["failures"] == 0, "Counterexample(s) found; see report"
    print("PASS: zero mismatches. Exhaustive finite sanity check completed; no general proof claimed.", flush=True)


if __name__ == "__main__":
    main()
