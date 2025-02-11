def get_value(fen: str) -> float:
    # Define piece and color constants.
    PAWN, KNIGHT, BISHOP, ROOK, QUEEN, KING = "P", "N", "B", "R", "Q", "K"
    WHITE, BLACK = "w", "b"

    # --- Helper Functions ---

    def parse_fen(fen: str):
        """
        Parses the FEN string into a board list and active color.
        The board is represented as a list of 64 squares (indices 0 to 63),
        where index 0 corresponds to A1 and 63 to H8.
        """
        parts = fen.split()
        board_part = parts[0]
        active_color = parts[1]
        rows = board_part.split('/')
        board = [None] * 64

        # FEN lists ranks from 8 (top) down to 1 (bottom).
        for row_index, row in enumerate(rows):
            rank = 8 - row_index  # Rank number: 8 for top row, 1 for bottom.
            file_index = 0
            for char in row:
                if char.isdigit():
                    file_index += int(char)
                else:
                    # Calculate square index:
                    # (rank - 1) * 8 gives the starting index for that rank.
                    square = (rank - 1) * 8 + file_index
                    board[square] = char
                    file_index += 1
        return board, active_color

    def square_rank(square: int) -> int:
        """Returns the rank (1 to 8) for a given square index."""
        return (square // 8) + 1

    def square_file(square: int) -> int:
        """Returns the file index (0 for A, 7 for H) for a given square index."""
        return square % 8

    def pieces(board, piece_type: str, color: str):
        """
        Returns a list of indices where pieces of the given type and color reside.
        White pieces are uppercase; black pieces are lowercase.
        """
        target = piece_type if color == WHITE else piece_type.lower()
        return [i for i, p in enumerate(board) if p == target]

    def king_square(board, color: str):
        """Returns the index of the king for the given color, or None if not found."""
        target = KING if color == WHITE else KING.lower()
        for i, p in enumerate(board):
            if p == target:
                return i
        return None

    # --- Evaluation Begins Here ---

    board, active_color = parse_fen(fen)
    value = 0
    xFromCen = [1, 2, 3, 4, 5, 3, 2, 1]  # A weight factor based on file proximity to the center.

    # Piece values for non-pawn pieces.
    piece_values = {
        PAWN: 1,
        KNIGHT: 3,
        BISHOP: 3,
        ROOK: 5,
        QUEEN: 9,
    }

    for tpe, val in piece_values.items():
        white_pcs = pieces(board, tpe, WHITE)
        black_pcs = pieces(board, tpe, BLACK)

        # Material balance.
        value += val * (len(white_pcs) - len(black_pcs))

        # Pawn-specific evaluation.
        if tpe == PAWN:
            for pawn_square in white_pcs:
                rank = square_rank(pawn_square)  # Ranks 1 (base) to 8 (promotion)
                file = square_file(pawn_square)
                # Reward advanced white pawns:
                value += 0.1 * xFromCen[file] * (rank - 1)
                if rank == 8:  # Pawn is promoted (or ready to be promoted)
                    value += 6
            for pawn_square in black_pcs:
                rank = square_rank(pawn_square)
                file = square_file(pawn_square)
                # For black pawns (which move downward), use the distance from rank 1.
                value -= 0.1 * xFromCen[file] * (8 - rank)
                if rank == 1:  # Black pawn is on its promotion rank
                    value -= 6

    # King positioning evaluation.
    w_king_sq = king_square(board, WHITE)
    b_king_sq = king_square(board, BLACK)

    if w_king_sq is not None:
        w_king_rank = square_rank(w_king_sq)
        w_king_file = square_file(w_king_sq)
        value += 0.5 * (0.2 * xFromCen[w_king_file] - w_king_rank)
    if b_king_sq is not None:
        b_king_rank = square_rank(b_king_sq)
        b_king_file = square_file(b_king_sq)
        value += 0.5 * ((0.2 * xFromCen[b_king_file]) + (7 - b_king_rank))

    # --- Penalty for Non-Pawn Pieces Remaining on Their Starting Squares ---

    # Define starting squares (using 0-63 indexing) for non-pawn pieces.
    white_starting = {
        KNIGHT: {1, 6},      # b1 and g1
        BISHOP: {2, 5},      # c1 and f1
        ROOK: {0, 7},        # a1 and h1
        QUEEN: {3},          # d1
        KING: {4},           # e1
    }
    black_starting = {
        KNIGHT: {57, 62},    # b8 and g8 (indices 57 and 62)
        BISHOP: {58, 61},    # c8 and f8
        ROOK: {56, 63},      # a8 and h8
        QUEEN: {59},         # d8
        KING: {60},          # e8
    }
    undeveloped_penalty = 0.1

    # For white pieces, subtract a small penalty if still on a starting square.
    for piece_type, starting_sqs in white_starting.items():
        for sq in pieces(board, piece_type, WHITE):
            if sq in starting_sqs:
                value -= undeveloped_penalty

    # For black pieces, add a penalty (which is good for white) if still on a starting square.
    for piece_type, starting_sqs in black_starting.items():
        for sq in pieces(board, piece_type, BLACK):
            if sq in starting_sqs:
                value += undeveloped_penalty

    return value