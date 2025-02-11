from Chessnut import Game
import random
import time

from typing import (
    List,
    Dict,
    Iterator,
)

# -----------------------------------------------------------------------------------------------

MAX_DEPTH = 1  # Adjust based on performance tests

def evaluate_board(game):
    material_values = {
        'p': 1, 'n': 3, 'b': 3, 'r': 5, 'q': 9, 'k': 0,  # black pieces
        'P': 1, 'N': 3, 'B': 3, 'R': 5, 'Q': 9, 'K': 0   # white pieces
    }
    score = 0
    # Convert the board to a string and remove newline characters.
    board_str = str(game.board).replace('\n', '')
    for piece in board_str:
        if piece in material_values:
            if piece.isupper():
                score += material_values[piece]
            else:
                score -= material_values[piece]
    return score

def minimax(game, depth, is_maximizing, alpha, beta, start_time, time_limit):
    # Here, 0 indicates an active game. Nonzero indicates a terminal state.
    if depth == 0 or game.status != 0:
        return evaluate_board(game), None

    best_move = None

    if is_maximizing:
        max_eval = -float('inf')
        for move in list(game.get_moves()):
            # Check time to avoid exceeding the time limit.
            if time.time() - start_time > time_limit:
                break

            # Create a new game state from the current FEN.
            g = Game(game.get_fen())
            g.apply_move(move)
            eval_score, _ = minimax(g, depth - 1, False, alpha, beta, start_time, time_limit)
            if eval_score > max_eval:
                max_eval = eval_score
                best_move = move
            alpha = max(alpha, eval_score)
            if beta <= alpha:
                break  # Beta cutoff
        return max_eval, best_move
    else:
        min_eval = float('inf')
        for move in list(game.get_moves()):
            if time.time() - start_time > time_limit:
                break

            g = Game(game.get_fen())
            g.apply_move(move)
            eval_score, _ = minimax(g, depth - 1, True, alpha, beta, start_time, time_limit)
            if eval_score < min_eval:
                min_eval = eval_score
                best_move = move
            beta = min(beta, eval_score)
            if beta <= alpha:
                break  # Alpha cutoff
        return min_eval, best_move

def chess_bot(obs):
    # Initialize the game state using the FEN provided in obs.board.
    game = Game(obs.board)

    legal_moves = list(game.get_moves())
    if not legal_moves:
        return "resign"

    start_time = time.time()
    time_limit = 9.0  # Leave a margin from the 10 seconds limit.
    best_move = None
    depth = 1  # Start with depth 1

    # Iterative deepening: gradually increase search depth.
    while time.time() - start_time < time_limit and depth <= MAX_DEPTH:
        _, move = minimax(game, depth, True, -float('inf'), float('inf'), start_time, time_limit)
        if move is not None:
            best_move = move
        if time.time() - start_time > time_limit:
            break
        depth += 1  # Increase depth for the next iteration

    return best_move if best_move else random.choice(legal_moves)
