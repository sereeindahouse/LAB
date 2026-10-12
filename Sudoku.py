from __future__ import annotations

import argparse
import json
import sys
from dataclasses import asdict, dataclass
from typing import TypeAlias

Board: TypeAlias = list[list[int]]
Cell: TypeAlias = tuple[int, int]
Domains: TypeAlias = dict[Cell, list[int]]
MODES = ("bt", "mrv", "mrv_degree", "mrv_degree_lcv")

STANDARD_PUZZLE = (
    "530070000/600195000/098000060/800060003/400803001/"
    "700020006/060000280/000419005/000080079"
)


def _make_peers(row: int, column: int) -> tuple[Cell, ...]:
    cells = {(row, c) for c in range(9)}
    cells.update((r, column) for r in range(9))
    top, left = row - row % 3, column - column % 3
    cells.update((r, c) for r in range(top, top + 3) for c in range(left, left + 3))
    cells.discard((row, column))
    return tuple(sorted(cells))


PEERS = {(r, c): _make_peers(r, c) for r in range(9) for c in range(9)}


class InvalidBoardError(ValueError):
    pass


@dataclass
class SearchStats:
    recursive_calls: int = 0
    placements: int = 0
    resets: int = 0
    validity_checks: int = 0
    domain_computations: int = 0


@dataclass
class SolveResult:
    solved: bool
    board: Board | None
    stats: SearchStats


def validate_board(board: Board) -> None:
    if not isinstance(board, (list, tuple)) or len(board) != 9:
        raise InvalidBoardError("Хүснэгт 9 мөртэй байх ёстой.")
    for row in board:
        if not isinstance(row, (list, tuple)) or len(row) != 9:
            raise InvalidBoardError("Мөр бүр 9 нүдтэй байх ёстой.")
        if any(type(value) is not int or not 0 <= value <= 9 for value in row):
            raise InvalidBoardError("Нүдний утга 0–9 бүхэл тоо байх ёстой.")
    for (r, c), peers in PEERS.items():
        value = board[r][c]
        if value and any(board[pr][pc] == value for pr, pc in peers):
            raise InvalidBoardError(
                f"Өгөгдсөн {value} тоо давхардсан: мөр {r + 1}, багана {c + 1}."
            )


def parse_puzzle(text: str) -> Board:
    rows = text.replace("/", " ").split()
    if len(rows) == 1 and len(rows[0]) == 81:
        rows = [rows[0][i:i + 9] for i in range(0, 81, 9)]
    if len(rows) != 9 or any(len(row) != 9 for row in rows):
        raise InvalidBoardError("Оролт 9×9 байх ёстой; хоосон нүдэнд 0 эсвэл . бичнэ.")
    if any(ch not in "0123456789." for row in rows for ch in row):
        raise InvalidBoardError("Зөвхөн 0–9 болон . тэмдэгт ашиглана.")
    board = [[0 if ch == "." else int(ch) for ch in row] for row in rows]
    validate_board(board)
    return board


def is_valid_move(
    board: Board, row: int, column: int, number: int,
    stats: SearchStats | None = None,
) -> bool:
    if stats is not None:
        stats.validity_checks += 1
    return all(board[r][c] != number for r, c in PEERS[(row, column)])


def candidate_domain(board: Board, cell: Cell, stats: SearchStats | None = None) -> list[int]:
    if stats is not None:
        stats.domain_computations += 1
    r, c = cell
    return [value for value in range(1, 10) if is_valid_move(board, r, c, value, stats)]


def compute_domains(board: Board, stats: SearchStats | None = None) -> Domains:
    return {
        (r, c): candidate_domain(board, (r, c), stats)
        for r in range(9) for c in range(9) if board[r][c] == 0
    }


def unassigned_degree(board: Board, cell: Cell) -> int:
    return sum(board[r][c] == 0 for r, c in PEERS[cell])


def select_variable(
    board: Board, mode: str, stats: SearchStats | None = None,
) -> tuple[Cell | None, list[int], Domains]:
    if mode not in MODES:
        raise ValueError(f"Тодорхойгүй горим: {mode}")
    if mode == "bt":
        for r in range(9):
            for c in range(9):
                if board[r][c] == 0:
                    return (r, c), list(range(1, 10)), {}
        return None, [], {}

    domains = compute_domains(board, stats)
    if not domains:
        return None, [], domains
    minimum = min(len(values) for values in domains.values())
    tied = [cell for cell, values in domains.items() if len(values) == minimum]
    if mode == "mrv":
        cell = min(tied)
    else:
        cell = min(tied, key=lambda item: (-unassigned_degree(board, item), item))
    return cell, domains[cell], domains


def lcv_impacts(cell: Cell, values: list[int], domains: Domains) -> dict[int, int]:
    return {
        value: sum(value in domains[peer] for peer in PEERS[cell] if peer in domains)
        for value in values
    }


def order_values(cell: Cell, values: list[int], domains: Domains, mode: str) -> list[int]:
    if mode != "mrv_degree_lcv":
        return sorted(values)
    impacts = lcv_impacts(cell, values, domains)
    return sorted(values, key=lambda value: (impacts[value], value))


def _search(board: Board, mode: str, stats: SearchStats) -> bool:
    stats.recursive_calls += 1
    cell, values, domains = select_variable(board, mode, stats)
    if cell is None:
        return True
    row, column = cell
    for value in order_values(cell, values, domains, mode):
        if mode == "bt" and not is_valid_move(board, row, column, value, stats):
            continue
        board[row][column] = value
        stats.placements += 1
        if _search(board, mode, stats):
            return True
        board[row][column] = 0
        stats.resets += 1
    return False


def solve(board: Board, mode: str = "mrv_degree_lcv") -> SolveResult:
    validate_board(board)
    if mode not in MODES:
        raise ValueError(f"Тодорхойгүй горим: {mode}")
    working = [list(row) for row in board]
    stats = SearchStats()
    solved = _search(working, mode, stats)
    return SolveResult(solved, working if solved else None, stats)


def format_board(board: Board) -> str:
    lines = []
    for r, row in enumerate(board):
        if r in (3, 6):
            lines.append("------+-------+------")
        chunks = [" ".join(str(v) if v else "." for v in row[i:i + 3]) for i in (0, 3, 6)]
        lines.append(" | ".join(chunks))
    return "\n".join(lines)


from statistics import median
from time import perf_counter
SOLUTION = "534678912/672195348/198342567/859761423/426853791/713924856/961537284/287419635/345286179"

PUZZLES = (
    {
        "name": "standard",
        "label_mn": "Стандарт бодлого",
        "grid": STANDARD_PUZZLE,
        "description_mn": "30 өгөгдсөн тоотой түгээмэл жишээ.",
    },
    {
        "name": "moderate",
        "label_mn": "Нэмэлт буцалт шаарддаг бодлого",
        "grid": "000600900/002000308/100040000/050001000/400050001/000004850/060007080/280419000/305080109",
        "description_mn": (
            "Ижил шийдээс тоонуудыг хасаж үүсгэсэн 28 өгөгдсөн тоотой бодлого. "
            "2029 seed-ийн дарааллаар нэг нэг нүд хасаж, нэг шийдтэйг хадгалсан."
        ),
    },
    {
        "name": "near_complete",
        "label_mn": "Бараг бөглөгдсөн бодлого",
        "grid": "034608912/602190348/190342067/859061403/426803790/013920856/901537084/280419605/345086170",
        "description_mn": "Бүрэн шийдийн мөр бүрээс хоёр нүд хассан: 63 өгөгдсөн тоо, 18 хоосон нүд.",
    },
)

EXAMPLE_GRID = "530600012/000005000/008040560/000701400/020800090/713000000/061000080/000419005/040000009"

def verify_solution(initial, solved):
    if len(solved) != 9 or any(len(row) != 9 for row in solved):
        raise AssertionError("Шийдийн хэмжээ 9×9 биш байна.")
    if any(type(value) is not int for row in solved for value in row):
        raise AssertionError("Шийдийн утгууд бүхэл тоо биш байна.")
    required = set(range(1, 10))
    if any(set(row) != required for row in solved):
        raise AssertionError("Шийдийн мөр бүр 1–9 тоог нэг нэг удаа агуулах ёстой.")
    if any({solved[r][c] for r in range(9)} != required for c in range(9)):
        raise AssertionError("Шийдийн багана бүр 1–9 тоог нэг нэг удаа агуулах ёстой.")
    for top in (0, 3, 6):
        for left in (0, 3, 6):
            block = {solved[r][c] for r in range(top, top + 3) for c in range(left, left + 3)}
            if block != required:
                raise AssertionError("Шийдийн 3×3 блок бүр 1–9 тоог нэг нэг удаа агуулах ёстой.")
    if any(initial[r][c] and initial[r][c] != solved[r][c]
           for r in range(9) for c in range(9)):
        raise AssertionError("Анхны өгөгдсөн тоо өөрчлөгдсөн.")

def benchmark_one(initial, mode, repeats=7):
    validate_board(initial)
    durations, previous_stats, final_board = [], None, None
    for _ in range(repeats):
        working = [row[:] for row in initial]
        stats = SearchStats()
        started = perf_counter()
        solved = _search(working, mode, stats)
        durations.append(perf_counter() - started)
        if not solved:
            raise AssertionError("Туршилтын бодлого шийдгүй байна.")
        verify_solution(initial, working)
        counters = asdict(stats)
        if previous_stats is not None and counters != previous_stats:
            raise AssertionError("Давталтуудад үйлдлийн тоо өөр байна.")
        previous_stats, final_board = counters, working
    return {
        "mode": mode,
        "repeats": repeats,
        "median_ms": median(durations) * 1000,
        "timings_seconds": durations,
        "stats": previous_stats,
        "solution": final_board,
    }

def make_worked_example():
    board = parse_puzzle(EXAMPLE_GRID)
    domains = compute_domains(board)
    minimum = min(len(values) for values in domains.values())
    selected, values, _ = select_variable(board, "mrv_degree_lcv")
    assert selected is not None
    impacts = lcv_impacts(selected, values, domains)

    def describe(cell):
        r, c = cell
        return {"row": r + 1, "column": c + 1, "cell": f"r{r + 1}c{c + 1}",
                "domain": domains[cell], "degree": unassigned_degree(board, cell)}

    return {
        "description_mn": (
            "Тусдаа тайлбарын бодлогын эхний төлөв. Мөр, баганыг 1-ээс дугаарлав. "
            "Бүх domain нь одоогийн өгөгдсөн тоонуудтай нийцэх утгууд."
        ),
        "grid": EXAMPLE_GRID,
        "minimum_domain_size": minimum,
        "all_unassigned_domains": [describe(cell) for cell in domains],
        "mrv_tied_cells": [describe(cell) for cell, domain in domains.items() if len(domain) == minimum],
        "mrv_choice": describe(select_variable(board, "mrv")[0]),
        "mrv_degree_choice": describe(selected),
        "lcv_impacts": [{"value": value, "eliminations": impacts[value]} for value in values],
        "lcv_order": order_values(selected, values, domains, "mrv_degree_lcv"),
    }

def compare_modes(repeats=7):
    if repeats < 1:
        raise ValueError("Давталтын тоо эерэг байх ёстой.")
    records = []
    print("Бодлого | Горим | Зангилаа | Буцалт | Медиан мс")
    for puzzle in PUZZLES:
        initial = parse_puzzle(puzzle["grid"])
        for mode in MODES:
            record = benchmark_one(initial, mode, repeats)
            record["puzzle"] = puzzle["name"]
            records.append(record)
            stats = record["stats"]
            print(f"{puzzle['name']} | {mode} | {stats['placements']} | "
                  f"{stats['resets']} | {record['median_ms']:.3f}")
    return records


def main():
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description="Sudoku: MRV, Degree, LCV")
    parser.add_argument("--mode", choices=MODES, default="mrv_degree_lcv")
    parser.add_argument("--puzzle", default=STANDARD_PUZZLE,
                        help="9 мөрийг / тэмдгээр тусгаарлана; 0 нь хоосон нүд.")
    parser.add_argument("--compare", action="store_true",
                        help="Тайлангийн гурван бодлогыг дөрвөн горимоор харьцуулах.")
    parser.add_argument("--repeats", type=int, default=7)
    args = parser.parse_args()
    try:
        if args.compare:
            compare_modes(args.repeats)
            return 0
        initial = parse_puzzle(args.puzzle)
        result = solve(initial, args.mode)
        if not result.solved:
            print("Хязгаарлалтад нийцэх шийд олдсонгүй.")
            return 1
        verify_solution(initial, result.board)
        print("Эхлэл:")
        print(format_board(initial))
        print("\nШийд:")
        print(format_board(result.board))
        print(f"Зангилаа: {result.stats.placements}; буцалт: {result.stats.resets}")
        return 0
    except (InvalidBoardError, ValueError) as error:
        print(f"Оролтын алдаа: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
