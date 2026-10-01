import sys
import random
import pygame

ROWS = 6
COLS = 7

CELL_SIZE = 90
TOP_SPACE = 190

WIDTH = COLS * CELL_SIZE
HEIGHT = ROWS * CELL_SIZE + TOP_SPACE

WINDOW_TITLE = "Connect Four - Minimax AI"

EMPTY = " "
PLAYER = -1
AI = 1

setDefaultDepth = 6
setScoreFor2 = 1
setScoreFor3 = 5
SEARCH_DEPTH = setDefaultDepth

FPS = 60

BACKGROUND = (25, 25, 35)
BOARD_COLOR = (30, 90, 180)
EMPTY_COLOR = (235, 235, 235)
PLAYER_COLOR = (220, 50, 55)
AI_COLOR = (245, 205, 45)
TEXT_COLOR = (245, 245, 245)
HIGHLIGHT_COLOR = (100, 220, 120)


MOVE_ORDER = (3, 2, 4, 1, 5, 0, 6)

# Every four-cell winning window, indexed once at startup.
wSlots = tuple(
    tuple((row + step * dr) * COLS + col + step * dc for step in range(4))
    for row in range(ROWS)
    for col in range(COLS)
    for dr, dc in ((0, 1), (1, 0), (1, 1), (1, -1))
    if 0 <= row + 3 * dr < ROWS and 0 <= col + 3 * dc < COLS
)
SLOTS_BY_CELL = tuple(
    tuple(line for line in wSlots if cell in line)
    for cell in range(ROWS * COLS)
)


class Connect4Board:
    """Report-style engine: X = +1, 0 = -1; row zero is at the top.

    Search returns -1/0/+1 only. Heuristics break ties at the root,
    not at search leaves. The bounded-score early exit in addPly is
    the report's pruning rule, rather than general alpha/beta bounds.
    """

    def __init__(self, board=None):
        self.board = EMPTY * (ROWS * COLS) if board is None else board
        if (not isinstance(self.board, str) or len(self.board) != 42
                or any(mark not in " X0" for mark in self.board)):
            raise ValueError("Board must contain 42 characters: space, X or 0")
        self.lastMove = None
        self.lastDecision = None

    @staticmethod
    def mark(player):
        if player not in (1, -1):
            raise ValueError("Player must be +1 or -1")
        return "X" if player == 1 else "0"

    def legitMoves(self):
        return [col for col in MOVE_ORDER if self.board[col] == EMPTY]

    def makeMove(self, player, col):
        mark = self.mark(player)
        if col not in self.legitMoves():
            raise ValueError("Column is invalid or full")
        for row in range(ROWS - 1, -1, -1):
            place = row * COLS + col
            if self.board[place] == EMPTY:
                self.board = self.board[:place] + mark + self.board[place + 1:]
                self.lastMove = place
                return self.winner()

    def winner(self):
        if self.lastMove is None:
            return ""
        mark = self.board[self.lastMove]
        if mark != EMPTY and any(
            all(self.board[cell] == mark for cell in line)
            for line in SLOTS_BY_CELL[self.lastMove]
        ):
            return mark
        return ""

    def instaWin(self, player):
        for col in self.legitMoves():
            child = Connect4Board(self.board)
            if child.makeMove(player, col) == self.mark(player):
                return col
        return -1

    def addPly(self, player, depth):
        self.mark(player)
        if depth <= 0:
            return 0
        results = []
        for col in self.legitMoves():
            child = Connect4Board(self.board)
            winner = child.makeMove(player, col)
            if winner == "" and depth > 1:
                result = child.addPly(-player, depth - 1)
            else:
                result = 0 if winner == "" else (1 if winner == "X" else -1)
            results.append(result)
            # Scores are bounded by [-1, 1]: this is already the best result.
            if result == player:
                return result
        return (max(results) if player == 1 else min(results)) if results else 0

    def minimax(self, player, depth=setDefaultDepth):
        self.mark(player)
        if depth < 1:
            raise ValueError("Depth must be at least one ply")
        scores = [None] * COLS  # Full columns have no score.
        for col in self.legitMoves():
            child = Connect4Board(self.board)
            winner = child.makeMove(player, col)
            if winner:
                scores[col] = 1 if winner == "X" else -1
            else:
                scores[col] = child.addPly(-player, depth - 1)
        return scores

    def getOneScore(self, player):
        mark, otherMark = self.mark(player), self.mark(-player)
        score = 0
        for line in wSlots:
            line_marks = [self.board[cell] for cell in line]
            if otherMark in line_marks:
                continue  # Skip this window, not all remaining windows.
            count = line_marks.count(mark)
            if count == 2:
                score += setScoreFor2
            elif count == 3:
                score += setScoreFor3
        return score

    def getScores(self, player):
        # Potential score if this player drops a piece into each column.
        scores = [None] * COLS
        for col in self.legitMoves():
            child = Connect4Board(self.board)
            child.makeMove(player, col)
            scores[col] = child.getOneScore(player)
        return scores

    def _decision(self, col, reason, scores=None, heuristic=None, verbose=False):
        self.lastDecision = dict(column=col, reason=reason,
                                 minimax=scores, heuristic=heuristic)
        if verbose:
            print("\n".join(self.decisionLines()))
        return col

    def decisionLines(self):
        if self.lastDecision is None:
            return ["AI: шийдвэр хараахан гараагүй"]
        d = self.lastDecision
        column = str(d['column'] + 1) if d['column'] >= 0 else "—"
        lines = [f"AI: {d['reason']} | багана {column}"]
        for label, key in (("Minimax (X)", "minimax"), ("Heuristic", "heuristic")):
            values = d[key]
            text = "алгассан" if values is None else "  ".join(
                f"{i + 1}:{'-' if value is None else value}"
                for i, value in enumerate(values)
            )
            lines.append(f"{label}: {text}")
        return lines

    def considerAll(self, player, minimax, pScores, nScores, verbose=False):
        moves = self.legitMoves()
        if not moves:
            return self._decision(-1, "Нүүдэл байхгүй", verbose=verbose)
        best = max(player * minimax[col] for col in moves)
        candidates = [col for col in moves if player * minimax[col] == best]
        # The report does not specify weights: use equal attack/defence weights.
        weights = [None if col not in moves else pScores[col] + nScores[col]
                   for col in range(COLS)]
        reason = "Minimax"
        if len(candidates) > 1:
            best_weight = max(weights[col] for col in candidates)
            candidates = [col for col in candidates if weights[col] == best_weight]
            reason = "Minimax + heuristic"
        if len(candidates) > 1:
            distance = min(abs(col - COLS // 2) for col in candidates)
            candidates = [col for col in candidates if abs(col - COLS // 2) == distance]
            reason += " + төв"
        if len(candidates) > 1:
            reason += " + санамсаргүй"
        return self._decision(random.choice(candidates), reason, minimax, weights, verbose)

    def chooseMove(self, player=1, depth=setDefaultDepth, verbose=False):
        self.mark(player)
        if depth < 1:
            raise ValueError("Depth must be at least one ply")
        if not self.legitMoves() or self.winner():
            return self._decision(-1, "Тоглолт дууссан", verbose=verbose)
        instawin = self.instaWin(player)
        if instawin != -1:
            return self._decision(instawin, "Шууд хожих", verbose=verbose)
        instalose = self.instaWin(-player)
        if instalose != -1:
            return self._decision(instalose, "Өрсөлдөгчийг хаах", verbose=verbose)
        minimax = self.minimax(player, depth)
        pScores = self.getScores(player)
        nScores = self.getScores(-player)
        return self.considerAll(player, minimax, pScores, nScores, verbose)


def create_board():
    return Connect4Board()


def valid_columns(board):
    return board.legitMoves()


def next_open_row(board, column):
    for row in range(ROWS - 1, -1, -1):
        if board.board[row * COLS + column] == EMPTY:
            return row
    return None


def drop_piece(board, row, column, piece):
    if row != next_open_row(board, column):
        raise ValueError("Piece must fall to the lowest empty cell")
    return board.makeMove(piece, column)


def board_full(board):
    return not board.legitMoves()


def winning_move(board, piece):
    return board.winner() == board.mark(piece)


def ai_move(board):
    column = board.chooseMove(AI, SEARCH_DEPTH, verbose=True)
    if column == -1:
        return False
    board.makeMove(AI, column)
    return True


def draw_text(screen, text, font, color, x, y):
    surface = font.render(text, True, color)
    screen.blit(surface, (x, y))


def draw_board(
    screen,
    board,
    font,
    small_font,
    hovered_column=None,
    message=""
):
    screen.fill(BACKGROUND)

    draw_text(
        screen,
        message,
        font,
        TEXT_COLOR,
        20,
        20
    )

    draw_text(
        screen,
        "Багана сонгоно уу | R = Дахин эхлүүлэх | ESC = Гарах",
        small_font,
        TEXT_COLOR,
        20,
        55
    )

    for index, line in enumerate(board.decisionLines()):
        draw_text(screen, line, small_font, TEXT_COLOR, 20, 85 + index * 25)

    pygame.draw.rect(
        screen,
        BOARD_COLOR,
        (0, TOP_SPACE, WIDTH, ROWS * CELL_SIZE)
    )

    if hovered_column is not None:
        pygame.draw.rect(
            screen,
            HIGHLIGHT_COLOR,
            (
                hovered_column * CELL_SIZE,
                TOP_SPACE,
                CELL_SIZE,
                ROWS * CELL_SIZE
            ),
            width=4
        )

    for row in range(ROWS):
        for column in range(COLS):
            center_x = (
                column * CELL_SIZE +
                CELL_SIZE // 2
            )

            center_y = (
                TOP_SPACE +
                row * CELL_SIZE +
                CELL_SIZE // 2
            )

            value = board.board[row * COLS + column]

            if value == "0":
                color = PLAYER_COLOR
            elif value == "X":
                color = AI_COLOR
            else:
                color = EMPTY_COLOR

            pygame.draw.circle(
                screen,
                color,
                (center_x, center_y),
                CELL_SIZE // 2 - 8
            )

            pygame.draw.circle(
                screen,
                BACKGROUND,
                (center_x, center_y),
                CELL_SIZE // 2 - 8,
                width=2
            )


def reset_game():
    return create_board(), False, ""


def main():
    pygame.init()

    screen = pygame.display.set_mode(
        (WIDTH, HEIGHT)
    )

    pygame.display.set_caption(WINDOW_TITLE)

    font = pygame.font.SysFont(
        "Arial",
        28,
        bold=True
    )

    small_font = pygame.font.SysFont(
        "Arial",
        18
    )

    clock = pygame.time.Clock()

    board = create_board()
    game_finished = False
    message = "Таны ээлж: улаан дискууд"

    while True:
        mouse_x, mouse_y = pygame.mouse.get_pos()
        hovered_column = (mouse_x // CELL_SIZE
                          if 0 <= mouse_x < WIDTH and TOP_SPACE <= mouse_y < HEIGHT
                          else None)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                sys.exit()

            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_ESCAPE:
                    pygame.quit()
                    sys.exit()

                if event.key == pygame.K_r:
                    board, game_finished, message = reset_game()
                    message = "Таны ээлж: улаан дискууд"

            if event.type == pygame.MOUSEMOTION:
                mouse_x, _ = event.pos

                if 0 <= mouse_x < WIDTH:
                    hovered_column = mouse_x // CELL_SIZE

            if (
                event.type == pygame.MOUSEBUTTONDOWN
                and not game_finished
            ):
                mouse_x, mouse_y = event.pos

                if event.button != 1 or not (0 <= mouse_x < WIDTH and TOP_SPACE <= mouse_y < HEIGHT):
                    continue

                column = mouse_x // CELL_SIZE

                if column not in valid_columns(board):
                    message = "Энэ багана дүүрсэн байна"
                    continue

                row = next_open_row(board, column)
                drop_piece(board, row, column, PLAYER)

                if winning_move(board, PLAYER):
                    message = "Та яллаа! R дарж дахин эхлүүлнэ үү"
                    game_finished = True
                    continue

                if board_full(board):
                    message = "Тэнцэв! R дарж дахин эхлүүлнэ үү"
                    game_finished = True
                    continue

                message = "AI бодож байна..."

                draw_board(
                    screen,
                    board,
                    font,
                    small_font,
                    hovered_column,
                    message
                )

                pygame.display.flip()

                ai_move(board)

                if winning_move(board, AI):
                    message = "AI яллаа! R дарж дахин эхлүүлнэ үү"
                    game_finished = True

                elif board_full(board):
                    message = "Тэнцэв! R дарж дахин эхлүүлнэ үү"
                    game_finished = True

                else:
                    message = "Таны ээлж: улаан дискууд"

        draw_board(
            screen,
            board,
            font,
            small_font,
            hovered_column,
            message
        )

        pygame.display.flip()
        clock.tick(FPS)


if __name__ == "__main__":
    main()
