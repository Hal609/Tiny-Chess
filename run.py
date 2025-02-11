from bot1 import Board, minimax
import random
import chess


def chess_bot(obs):
    print(obs.board)

    game = Board(obs.board)
    moves = list(game.legal_moves)

    _, move = minimax(
        game,
        depth=4,
        alpha=-float("inf"),
        beta=float("inf"),
        maximizingPlayer=game.turn,
    )

    print(move)

    if move is None:
        move = random.choice(list(game.legal_moves))

    return str(move)
