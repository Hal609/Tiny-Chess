import chess
import chess.pgn 



for i in range(100):
    board = chess.Board() 
    name = f"D{i:02}"
    try:
        pgn = open(f"opening_dl/{name}.pgn")
    except:
        next
    game = chess.pgn.read_game(pgn) 

    print(f"# {name}")
    for number, move in enumerate(game.mainline_moves()): 
        # split = board.fen().split()
        # print(f'"{split[0]} {split[1]}": "{move}",')
        print(f'"{board.fen()}": "{move}",')
        board.push(move)
        if number >= 5:
            break
