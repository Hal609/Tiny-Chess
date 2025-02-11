import random
import time
from helper import get_value
from my_extension import get_move

WHITE: bool = True
BLACK: bool = False
COLORS = [WHITE, BLACK]

PAWN: int = 1
KNIGHT: int = 2
BISHOP: int = 3
ROOK: int = 4
QUEEN: int = 5
KING: int = 6
PIECE_SYMBOLS = [None, "p", "n", "b", "r", "q", "k"]

def piece_symbol(tpe: int) -> str:
    return str(PIECE_SYMBOLS[tpe])


FILE_NAMES = ["a", "b", "c", "d", "e", "f", "g", "h"]
RANK_NAMES = ["1", "2", "3", "4", "5", "6", "7", "8"]

SQUARES_DICT = {
    str(chr(65 + col)) + str(row): row * 8 + col
    for row in range(1, 9)
    for col in range(8)
}
SQUARES = list(range(64))
SQUARE_NAMES = [f + r for r in RANK_NAMES for f in FILE_NAMES]


def square_file(square: int) -> int:
    return square & 7


def square_rank(square: int) -> int:
    return square >> 3


def square_distance(a: int, b: int) -> int:
    return max(
        abs(square_file(a) - square_file(b)), abs(square_rank(a) - square_rank(b))
    )


def square_mirror(square: int) -> int:
    return square ^ 0x38


SQUARES_180= [square_mirror(sq) for sq in SQUARES]

BB_EMPTY: int = 0
BB_ALL: int = 0xFFFF_FFFF_FFFF_FFFF

SQUARES_DICT = {
    str(chr(65 + col)) + str(row): row * 8 + col
    for row in range(1, 9)
    for col in range(8)
}
BB_DICT = {"BB_" + str(square): 1 << index for square, index in SQUARES_DICT.items()}
BB_SQUARES = [1 << sq for sq in SQUARES]

BB_LIGHT_SQUARES: int = 0x55AA_55AA_55AA_55AA
BB_DARK_SQUARES: int = 0xAA55_AA55_AA55_AA55

BB_FL_A: int = 0x0101_0101_0101_0101 << 0
BB_FL_B: int = 0x0101_0101_0101_0101 << 1
BB_FL_C: int = 0x0101_0101_0101_0101 << 2
BB_FL_D: int = 0x0101_0101_0101_0101 << 3
BB_FL_E: int = 0x0101_0101_0101_0101 << 4
BB_FL_F: int = 0x0101_0101_0101_0101 << 5
BB_FL_G: int = 0x0101_0101_0101_0101 << 6
BB_FL_H: int = 0x0101_0101_0101_0101 << 7
BB_FLS = [
    BB_FL_A,
    BB_FL_B,
    BB_FL_C,
    BB_FL_D,
    BB_FL_E,
    BB_FL_F,
    BB_FL_G,
    BB_FL_H,
]

BB_RK_1: int = 0xFF << (8 * 0)
BB_RK_2: int = 0xFF << (8 * 1)
BB_RK_3: int = 0xFF << (8 * 2)
BB_RK_4: int = 0xFF << (8 * 3)
BB_RK_5: int = 0xFF << (8 * 4)
BB_RK_6: int = 0xFF << (8 * 5)
BB_RK_7: int = 0xFF << (8 * 6)
BB_RK_8: int = 0xFF << (8 * 7)
BB_RKS = [
    BB_RK_1,
    BB_RK_2,
    BB_RK_3,
    BB_RK_4,
    BB_RK_5,
    BB_RK_6,
    BB_RK_7,
    BB_RK_8,
]

BB_BACKRANKS: int = BB_RK_1 | BB_RK_8


def lsb(bb: int) -> int:
    return (bb & -bb).bit_length() - 1


def scan_forward(bb: int):
    while bb:
        r = bb & -bb
        yield r.bit_length() - 1
        bb ^= r


def msb(bb: int) -> int:
    return bb.bit_length() - 1


def scan_reversed(bb: int):
    while bb:
        r = bb.bit_length() - 1
        yield r
        bb ^= BB_SQUARES[r]


popcount = getattr(
    int, "bit_count", lambda bb: bin(bb).count("1")
)


def _sliding_attacks(square: int, occupied: int, deltas) -> int:
    attacks = BB_EMPTY
    for delta in deltas:
        sq = square

        while True:
            sq += delta
            if not (0 <= sq < 64) or square_distance(sq, sq - delta) > 2:
                break

            attacks |= BB_SQUARES[sq]

            if occupied & BB_SQUARES[sq]:
                break
    return attacks


def _step_attacks(square: int, deltas) -> int:
    return _sliding_attacks(square, BB_ALL, deltas)


BB_KNIGHT_ATTACKS = [
    _step_attacks(sq, [17, 15, 10, 6, -17, -15, -10, -6]) for sq in SQUARES
]
BB_KING_ATTACKS = [
    _step_attacks(sq, [9, 8, 7, 1, -9, -8, -7, -1]) for sq in SQUARES
]
BB_PAWN_ATTACKS = [
    [_step_attacks(sq, deltas) for sq in SQUARES] for deltas in [[-7, -9], [7, 9]]
]


def _edges(square: int) -> int:
    return ((BB_RK_1 | BB_RK_8) & ~BB_RKS[square_rank(square)]) | (
        (BB_FL_A | BB_FL_H) & ~BB_FLS[square_file(square)]
    )


def _carry_rippler(mask: int):
    subset = BB_EMPTY
    while True:
        yield subset
        subset = (subset - mask) & mask
        if not subset:
            break


def _attack_table(deltas):
    mask_table = []
    attack_table = []

    for square in SQUARES:
        attacks = {}
        mask = _sliding_attacks(square, 0, deltas) & ~_edges(square)
        for subset in _carry_rippler(mask):
            attacks[subset] = _sliding_attacks(square, subset, deltas)

        attack_table.append(attacks)
        mask_table.append(mask)

    return mask_table, attack_table


BB_DIAG_MASKS, BB_DIAG_ATTACKS = _attack_table([-9, -7, 7, 9])
BB_FL_MASKS, BB_FL_ATTACKS = _attack_table([-8, 8])
BB_RK_MASKS, BB_RK_ATTACKS = _attack_table([-1, 1])


def _rays():
    rays = []
    for a, bb_a in enumerate(BB_SQUARES):
        rays_row = []
        for b, bb_b in enumerate(BB_SQUARES):
            if BB_DIAG_ATTACKS[a][0] & bb_b:
                rays_row.append(
                    (BB_DIAG_ATTACKS[a][0] & BB_DIAG_ATTACKS[b][0]) | bb_a | bb_b
                )
            elif BB_RK_ATTACKS[a][0] & bb_b:
                rays_row.append(BB_RK_ATTACKS[a][0] | bb_a)
            elif BB_FL_ATTACKS[a][0] & bb_b:
                rays_row.append(BB_FL_ATTACKS[a][0] | bb_a)
            else:
                rays_row.append(BB_EMPTY)
        rays.append(rays_row)
    return rays


BB_RAYS = _rays()


def ray(a: int, b: int) -> int:
    return BB_RAYS[a][b]


def between(a: int, b: int) -> int:
    bb = BB_RAYS[a][b] & ((BB_ALL << a) ^ (BB_ALL << b))
    return bb & (bb - 1)


def from_symbol(symbol: str):
    return PIECE_SYMBOLS.index(symbol.lower()), symbol.isupper()


class Move:
    from_square: int
    to_square: int
    promotion = None
    drop = None

    def __init__(self, from_sq, to_sq, prom=None, drp=None):
        self.from_square = from_sq
        self.to_square = to_sq
        self.promotion = prom
        self.drop = drp

    def uci(self) -> str:
        if self.drop:
            return piece_symbol(self.drop).upper() + "@" + SQUARE_NAMES[self.to_square]
        elif self.promotion:
            return (
                SQUARE_NAMES[self.from_square]
                + SQUARE_NAMES[self.to_square]
                + piece_symbol(self.promotion)
            )
        elif self:
            return SQUARE_NAMES[self.from_square] + SQUARE_NAMES[self.to_square]
        else:
            return "0000"

    def __str__(self) -> str:
        return self.uci()


class BaseBoard:
    def __init__(self, board_fen: str) -> None:
        self.occupied_co = [BB_EMPTY, BB_EMPTY]

    def reset_board(self) -> None:
        self._reset_board()

    def _clear_board(self) -> None:
        self.pawns = BB_EMPTY
        self.knights = BB_EMPTY
        self.bishops = BB_EMPTY
        self.rooks = BB_EMPTY
        self.queens = BB_EMPTY
        self.kings = BB_EMPTY

        self.promoted = BB_EMPTY

        self.occupied_co[WHITE] = BB_EMPTY
        self.occupied_co[BLACK] = BB_EMPTY
        self.occupied = BB_EMPTY

    def pieces_mask(self, tpe: int, color: int) -> int:
        if tpe == PAWN:
            bb = self.pawns
        elif tpe == KNIGHT:
            bb = self.knights
        elif tpe == BISHOP:
            bb = self.bishops
        elif tpe == ROOK:
            bb = self.rooks
        elif tpe == QUEEN:
            bb = self.queens
        elif tpe == KING:
            bb = self.kings

        return bb & self.occupied_co[color]

    def pieces(self, tpe: int, color: int):
        return intSet(self.pieces_mask(tpe, color))

    def tpe_at(self, square: int):
        mask = BB_SQUARES[square]
        if not self.occupied & mask:
            return None
        elif self.pawns & mask:
            return PAWN
        elif self.knights & mask:
            return KNIGHT
        elif self.bishops & mask:
            return BISHOP
        elif self.rooks & mask:
            return ROOK
        elif self.queens & mask:
            return QUEEN
        else:
            return KING

    def king(self, color: int):
        king_mask = self.occupied_co[color] & self.kings & ~self.promoted
        return msb(king_mask) if king_mask else None

    def attacks_mask(self, square: int) -> int:
        bb_square = BB_SQUARES[square]

        if bb_square & self.pawns:
            color = bool(bb_square & self.occupied_co[WHITE])
            return BB_PAWN_ATTACKS[color][square]
        elif bb_square & self.knights:
            return BB_KNIGHT_ATTACKS[square]
        elif bb_square & self.kings:
            return BB_KING_ATTACKS[square]
        else:
            attacks = 0
            if bb_square & self.bishops or bb_square & self.queens:
                attacks = BB_DIAG_ATTACKS[square][BB_DIAG_MASKS[square] & self.occupied]
            if bb_square & self.rooks or bb_square & self.queens:
                attacks |= (
                    BB_RK_ATTACKS[square][BB_RK_MASKS[square] & self.occupied]
                    | BB_FL_ATTACKS[square][BB_FL_MASKS[square] & self.occupied]
                )
            return attacks

    def attackers_mask(
        self, color: int, square: int, occupied = None
    ) -> int:
        occupied = self.occupied if occupied is None else occupied

        rank_pieces = BB_RK_MASKS[square] & occupied
        file_pieces = BB_FL_MASKS[square] & occupied
        diag_pieces = BB_DIAG_MASKS[square] & occupied

        queens_and_rooks = self.queens | self.rooks
        queens_and_bishops = self.queens | self.bishops

        attackers = (
            (BB_KING_ATTACKS[square] & self.kings)
            | (BB_KNIGHT_ATTACKS[square] & self.knights)
            | (BB_RK_ATTACKS[square][rank_pieces] & queens_and_rooks)
            | (BB_FL_ATTACKS[square][file_pieces] & queens_and_rooks)
            | (BB_DIAG_ATTACKS[square][diag_pieces] & queens_and_bishops)
            | (BB_PAWN_ATTACKS[not color][square] & self.pawns)
        )

        return attackers & self.occupied_co[color]

    def is_attacked_by(self, color: int, square: int, occupied=None) -> bool:
        return bool(
            self.attackers_mask(
                color, square, None if occupied is None else intSet(occupied).mask
            )
        )

    def pin_mask(self, color: int, square: int) -> int:
        king = self.king(color)
        if king is None:
            return BB_ALL

        square_mask = BB_SQUARES[square]

        for attacks, sliders in [
            (BB_FL_ATTACKS, self.rooks | self.queens),
            (BB_RK_ATTACKS, self.rooks | self.queens),
            (BB_DIAG_ATTACKS, self.bishops | self.queens),
        ]:
            rays = attacks[king][0]
            if rays & square_mask:
                snipers = rays & sliders & self.occupied_co[not color]
                for sniper in scan_reversed(snipers):
                    if (
                        between(sniper, king) & (self.occupied | square_mask)
                        == square_mask
                    ):
                        return ray(king, sniper)

                break

        return BB_ALL

    def _remove_piece_at(self, square: int):
        tpe = self.tpe_at(square)
        mask = BB_SQUARES[square]

        if tpe == PAWN:
            self.pawns ^= mask
        elif tpe == KNIGHT:
            self.knights ^= mask
        elif tpe == BISHOP:
            self.bishops ^= mask
        elif tpe == ROOK:
            self.rooks ^= mask
        elif tpe == QUEEN:
            self.queens ^= mask
        elif tpe == KING:
            self.kings ^= mask
        else:
            return None

        self.occupied ^= mask
        self.occupied_co[WHITE] &= ~mask
        self.occupied_co[BLACK] &= ~mask

        self.promoted &= ~mask

        return tpe

    def _set_piece_at(
        self,
        square: int,
        tpe: int,
        color: int,
        promoted: bool = False,
    ) -> None:
        self._remove_piece_at(square)

        mask = BB_SQUARES[square]

        if tpe == PAWN:
            self.pawns |= mask
        elif tpe == KNIGHT:
            self.knights |= mask
        elif tpe == BISHOP:
            self.bishops |= mask
        elif tpe == ROOK:
            self.rooks |= mask
        elif tpe == QUEEN:
            self.queens |= mask
        elif tpe == KING:
            self.kings |= mask
        else:
            return

        self.occupied ^= mask
        self.occupied_co[color] ^= mask

        if promoted:
            self.promoted ^= mask

    def _set_board_fen(self, fen: str) -> None:
        fen = fen.strip()
        rows = fen.split("/")
        for row in rows:
            field_sum = 0
            previous_was_digit = False
            previous_was_piece = False
            for c in row:
                if c in ["1", "2", "3", "4", "5", "6", "7", "8"]:
                    field_sum += int(c)
                    previous_was_digit = True
                    previous_was_piece = False
                elif c == "~":
                    previous_was_digit = False
                    previous_was_piece = False
                elif c.lower() in PIECE_SYMBOLS:
                    field_sum += 1
                    previous_was_digit = False
                    previous_was_piece = True

        self._clear_board()

        square_index = 0
        for c in fen:
            if c in ["1", "2", "3", "4", "5", "6", "7", "8"]:
                square_index += int(c)
            elif c.lower() in PIECE_SYMBOLS:
                piece_type, piece_colour = from_symbol(c)
                self._set_piece_at(SQUARES_180[square_index], piece_type, piece_colour)
                square_index += 1
            elif c == "~":
                self.promoted |= BB_SQUARES[SQUARES_180[square_index - 1]]


class _BoardState:
    def __init__(self, board) -> None:
        self.pawns = board.pawns
        self.knights = board.knights
        self.bishops = board.bishops
        self.rooks = board.rooks
        self.queens = board.queens
        self.kings = board.kings

        self.occupied_w = board.occupied_co[WHITE]
        self.occupied_b = board.occupied_co[BLACK]
        self.occupied = board.occupied

        self.promoted = board.promoted

        self.turn = board.turn
        self.castling_rights = board.castling_rights
        self.ep_square = board.ep_square
        self.halfmove_clock = board.halfmove_clock
        self.fullmove_number = board.fullmove_number

    def restore(self, board) -> None:
        board.pawns = self.pawns
        board.knights = self.knights
        board.bishops = self.bishops
        board.rooks = self.rooks
        board.queens = self.queens
        board.kings = self.kings

        board.occupied_co[WHITE] = self.occupied_w
        board.occupied_co[BLACK] = self.occupied_b
        board.occupied = self.occupied

        board.promoted = self.promoted

        board.turn = self.turn
        board.castling_rights = self.castling_rights
        board.ep_square = self.ep_square
        board.halfmove_clock = self.halfmove_clock
        board.fullmove_number = self.fullmove_number


class Board(BaseBoard):
    def __init__(self, fen: str, *, chess960: bool = False) -> None:
        BaseBoard.__init__(self, None)

        self.chess960 = chess960

        self.ep_square = None
        self.move_stack = []
        self._stack = []

        if fen is None:
            self.clear()
        else:
            self.set_fen(fen)

    @property
    def legal_moves(self):
        return LegalMoveGenerator(self)

    def clear_stack(self) -> None:
        self.move_stack.clear()
        self._stack.clear()
        
    def piece_at(self, square):
        piece_type = self.piece_type_at(square)
        if piece_type:
            mask = BB_SQUARES[square]
            color = bool(self.occupied_co[WHITE] & mask)
            return (piece_type, color)
        else:
            return None, None

    def piece_type_at(self, square):
        mask = BB_SQUARES[square]

        if not self.occupied & mask:
            return None  # Early return
        elif self.pawns & mask:
            return PAWN
        elif self.knights & mask:
            return KNIGHT
        elif self.bishops & mask:
            return BISHOP
        elif self.rooks & mask:
            return ROOK
        elif self.queens & mask:
            return QUEEN
        else:
            return KING
    
    def board_fen(self, *, promoted:bool = False) -> str:
        builder = []
        empty = 0

        for square in SQUARES_180:
            piece_type, piece_colour = self.piece_at(square)

            if not piece_type:
                empty += 1
            else:
                if empty:
                    builder.append(str(empty))
                    empty = 0
                symbol = str(PIECE_SYMBOLS[piece_type])
                if piece_colour: symbol = symbol.upper()
                builder.append(symbol)
                if promoted and BB_SQUARES[square] & self.promoted:
                    builder.append("~")

            BB_FILE_H: int = 0x0101_0101_0101_0101 << 7
            if BB_SQUARES[square] & BB_FILE_H:
                if empty:
                    builder.append(str(empty))
                    empty = 0

                if square != SQUARES_180[-1]:
                    builder.append("/")
        return "".join(builder)
    
    def generate_pseudo_legal_moves(
        self, from_mask: int = BB_ALL, to_mask: int = BB_ALL
    ):
        our_pieces = self.occupied_co[self.turn]

        non_pawns = our_pieces & ~self.pawns & from_mask
        for from_square in scan_reversed(non_pawns):
            moves = self.attacks_mask(from_square) & ~our_pieces & to_mask
            for to_square in scan_reversed(moves):
                yield Move(from_square, to_square)

        if from_mask & self.kings:
            yield from self.generate_castling_moves(from_mask, to_mask)

        pawns = self.pawns & self.occupied_co[self.turn] & from_mask
        if not pawns:
            return

        capturers = pawns
        for from_square in scan_reversed(capturers):
            targets = (
                BB_PAWN_ATTACKS[self.turn][from_square]
                & self.occupied_co[not self.turn]
                & to_mask
            )

            for to_square in scan_reversed(targets):
                if square_rank(to_square) in [0, 7]:
                    yield Move(from_square, to_square, QUEEN)
                    yield Move(from_square, to_square, ROOK)
                    yield Move(from_square, to_square, BISHOP)
                    yield Move(from_square, to_square, KNIGHT)
                else:
                    yield Move(from_square, to_square)

        if self.turn == WHITE:
            single_moves = pawns << 8 & ~self.occupied
            double_moves = single_moves << 8 & ~self.occupied & (BB_RK_3 | BB_RK_4)
        else:
            single_moves = pawns >> 8 & ~self.occupied
            double_moves = single_moves >> 8 & ~self.occupied & (BB_RK_6 | BB_RK_5)

        single_moves &= to_mask
        double_moves &= to_mask

        for to_square in scan_reversed(single_moves):
            from_square = to_square + (8 if self.turn == BLACK else -8)

            if square_rank(to_square) in [0, 7]:
                yield Move(from_square, to_square, QUEEN)
                yield Move(from_square, to_square, ROOK)
                yield Move(from_square, to_square, BISHOP)
                yield Move(from_square, to_square, KNIGHT)
            else:
                yield Move(from_square, to_square)

        for to_square in scan_reversed(double_moves):
            from_square = to_square + (16 if self.turn == BLACK else -16)
            yield Move(from_square, to_square)

        if self.ep_square:
            yield from self.generate_pseudo_legal_ep(from_mask, to_mask)

    def generate_pseudo_legal_ep(
        self, from_mask: int = BB_ALL, to_mask: int = BB_ALL
    ):
        if not self.ep_square or not BB_SQUARES[self.ep_square] & to_mask:
            return

        if BB_SQUARES[self.ep_square] & self.occupied:
            return

        capturers = (
            self.pawns
            & self.occupied_co[self.turn]
            & from_mask
            & BB_PAWN_ATTACKS[not self.turn][self.ep_square]
            & BB_RKS[4 if self.turn else 3]
        )

        for capturer in scan_reversed(capturers):
            yield Move(capturer, self.ep_square)

    def checkers_mask(self) -> int:
        king = self.king(self.turn)
        return BB_EMPTY if king is None else self.attackers_mask(not self.turn, king)

    def is_check(self) -> bool:
        return bool(self.checkers_mask())

    def gives_check(self, move: Move) -> bool:
        self.push(move)
        try:
            return self.is_check()
        finally:
            self.pop()

    def is_checkmate(self) -> bool:
        if not self.is_check():
            return False
        return not any(self.generate_legal_moves())

    def is_stalemate(self) -> bool:
        if self.is_check():
            return False
        return not any(self.generate_legal_moves())

    def is_insufficient_material(self) -> bool:
        return all(self.has_insufficient_material(color) for color in COLORS)

    def has_insufficient_material(self, color: int) -> bool:
        if self.occupied_co[color] & (self.pawns | self.rooks | self.queens):
            return False

        if self.occupied_co[color] & self.knights:
            return popcount(self.occupied_co[color]) <= 2 and not (
                self.occupied_co[not color] & ~self.kings & ~self.queens
            )

        if self.occupied_co[color] & self.bishops:
            same_color = (not self.bishops & BB_DARK_SQUARES) or (
                not self.bishops & BB_LIGHT_SQUARES
            )
            return same_color and not self.pawns and not self.knights

        return True

    def is_fivefold_repetition(self) -> bool:
        return self.is_repetition(5)

    def is_repetition(self, count: int = 3) -> bool:
        maybe_repetitions = 1
        for state in reversed(self._stack):
            if state.occupied == self.occupied:
                maybe_repetitions += 1
                if maybe_repetitions >= count:
                    break
        if maybe_repetitions < count:
            return False

        transposition_key = self._transposition_key()
        switchyard = []

        try:
            while True:
                if count <= 1:
                    return True

                if len(self.move_stack) < count - 1:
                    break

                move = self.pop()
                switchyard.append(move)

                if self.is_irreversible(move):
                    break

                if self._transposition_key() == transposition_key:
                    count -= 1
        finally:
            while switchyard:
                self.push(switchyard.pop())

        return False

    def push(self, move: Move) -> None:
        move = self._to_chess960(move)
        board_state = _BoardState(self)
        self.castling_rights = self.clean_castling_rights()
        self.move_stack.append(
            self._from_chess960(
                self.chess960,
                move.from_square,
                move.to_square,
                move.promotion,
                move.drop,
            )
        )
        self._stack.append(board_state)
        ep_square = self.ep_square
        self.ep_square = None
        self.halfmove_clock += 1
        if self.turn == BLACK:
            self.fullmove_number += 1
        if not move:
            self.turn = not self.turn
            return
        if move.drop:
            self._set_piece_at(move.to_square, move.drop, self.turn)
            self.turn = not self.turn
            return
        if self.is_zeroing(move):
            self.halfmove_clock = 0
        from_bb = BB_SQUARES[move.from_square]
        to_bb = BB_SQUARES[move.to_square]

        promoted = bool(self.promoted & from_bb)
        tpe = self._remove_piece_at(move.from_square)
        capture_square = move.to_square
        captured_tpe = self.tpe_at(capture_square)

        self.castling_rights &= ~to_bb & ~from_bb
        if tpe == KING and not promoted:
            if self.turn == WHITE:
                self.castling_rights &= ~BB_RK_1
            else:
                self.castling_rights &= ~BB_RK_8
        elif captured_tpe == KING and not self.promoted & to_bb:
            if self.turn == WHITE and square_rank(move.to_square) == 7:
                self.castling_rights &= ~BB_RK_8
            elif self.turn == BLACK and square_rank(move.to_square) == 0:
                self.castling_rights &= ~BB_RK_1

        if tpe == PAWN:
            diff = move.to_square - move.from_square

            if diff == 16 and square_rank(move.from_square) == 1:
                self.ep_square = move.from_square + 8
            elif diff == -16 and square_rank(move.from_square) == 6:
                self.ep_square = move.from_square - 8
            elif (
                move.to_square == ep_square and abs(diff) in [7, 9] and not captured_tpe
            ):

                down = -8 if self.turn == WHITE else 8
                capture_square = ep_square + down
                captured_tpe = self._remove_piece_at(capture_square)

        if move.promotion:
            promoted = True
            tpe = move.promotion

        castling = tpe == KING and self.occupied_co[self.turn] & to_bb
        if castling:
            a_side = square_file(move.to_square) < square_file(move.from_square)

            self._remove_piece_at(move.from_square)
            self._remove_piece_at(move.to_square)

            if a_side:
                self._set_piece_at(
                    SQUARES_DICT["C1"] if self.turn == WHITE else SQUARES_DICT[" 8"],
                    KING,
                    self.turn,
                )
                self._set_piece_at(
                    SQUARES_DICT["D1"] if self.turn == WHITE else SQUARES_DICT["D8"],
                    ROOK,
                    self.turn,
                )
            else:
                self._set_piece_at(
                    SQUARES_DICT["G1"] if self.turn == WHITE else SQUARES_DICT["G8"],
                    KING,
                    self.turn,
                )
                self._set_piece_at(
                    SQUARES_DICT["F1"] if self.turn == WHITE else SQUARES_DICT["F8"],
                    ROOK,
                    self.turn,
                )

        if not castling:
            self._set_piece_at(move.to_square, tpe, self.turn, promoted)

        self.turn = not self.turn

    def pop(self) -> Move:
        move = self.move_stack.pop()
        self._stack.pop().restore(self)
        return move

    def set_fen(self, fen: str) -> None:

        parts = fen.split()
        board_part = parts.pop(0)

        turn_part = parts.pop(0)
        turn = WHITE if turn_part == "w" else BLACK
        castling_part = parts.pop(0)

        ep_part = parts.pop(0)
        ep_square = None if ep_part == "-" else SQUARE_NAMES.index(ep_part)

        halfmove_part = parts.pop(0)
        halfmove_clock = int(halfmove_part)

        fullmove_part = parts.pop(0)
        fullmove_number = int(fullmove_part)
        fullmove_number = max(fullmove_number, 1)

        self._set_board_fen(board_part)
        self.turn = turn
        self._set_castling_fen(castling_part)
        self.ep_square = ep_square
        self.halfmove_clock = halfmove_clock
        self.fullmove_number = fullmove_number
        self.clear_stack()

    def _set_castling_fen(self, castling_fen: str) -> None:
        if not castling_fen or castling_fen == "-":
            self.castling_rights = BB_EMPTY
            return

        self.castling_rights = BB_EMPTY

        for flag in castling_fen:
            color = WHITE if flag.isupper() else BLACK
            flag = flag.lower()
            backrank = BB_RK_1 if color == WHITE else BB_RK_8
            rooks = self.occupied_co[color] & self.rooks & backrank
            king = self.king(color)

            if flag == "q":
                if king is not None and lsb(rooks) < king:
                    self.castling_rights |= rooks & -rooks
                else:
                    self.castling_rights |= BB_FL_A & backrank
            elif flag == "k":
                rook = msb(rooks)
                if king is not None and king < rook:
                    self.castling_rights |= BB_SQUARES[rook]
                else:
                    self.castling_rights |= BB_FL_H & backrank
            else:
                self.castling_rights |= BB_FLS[FILE_NAMES.index(flag)] & backrank

    def is_en_passant(self, move: Move) -> bool:
        return (
            self.ep_square == move.to_square
            and bool(self.pawns & BB_SQUARES[move.from_square])
            and abs(move.to_square - move.from_square) in [7, 9]
            and not self.occupied & BB_SQUARES[move.to_square]
        )

    def is_capture(self, move: Move) -> bool:
        touched = BB_SQUARES[move.from_square] ^ BB_SQUARES[move.to_square]
        return bool(touched & self.occupied_co[not self.turn]) or self.is_en_passant(
            move
        )

    def is_zeroing(self, move: Move) -> bool:
        touched = BB_SQUARES[move.from_square] ^ BB_SQUARES[move.to_square]
        return bool(
            touched & self.pawns
            or touched & self.occupied_co[not self.turn]
            or move.drop == PAWN
        )

    def is_castling(self, move: Move) -> bool:
        if self.kings & BB_SQUARES[move.from_square]:
            diff = square_file(move.from_square) - square_file(move.to_square)
            return abs(diff) > 1 or bool(
                self.rooks & self.occupied_co[self.turn] & BB_SQUARES[move.to_square]
            )
        return False

    def clean_castling_rights(self) -> int:
        if self._stack:
            return self.castling_rights

        castling = self.castling_rights & self.rooks
        white_castling = castling & BB_RK_1 & self.occupied_co[WHITE]
        black_castling = castling & BB_RK_8 & self.occupied_co[BLACK]

        if not self.chess960:

            white_castling &= BB_DICT["BB_A1"] | BB_DICT["BB_H1"]
            black_castling &= BB_DICT["BB_A8"] | BB_DICT["BB_H8"]

            if (
                not self.occupied_co[WHITE]
                & self.kings
                & ~self.promoted
                & BB_DICT["BB_E1"]
            ):
                white_castling = 0
            if (
                not self.occupied_co[BLACK]
                & self.kings
                & ~self.promoted
                & BB_DICT["BB_E8"]
            ):
                black_castling = 0

            return white_castling | black_castling
        else:

            white_king_mask = (
                self.occupied_co[WHITE] & self.kings & BB_RK_1 & ~self.promoted
            )
            black_king_mask = (
                self.occupied_co[BLACK] & self.kings & BB_RK_8 & ~self.promoted
            )
            if not white_king_mask:
                white_castling = 0
            if not black_king_mask:
                black_castling = 0

            white_a_side = white_castling & -white_castling
            white_h_side = BB_SQUARES[msb(white_castling)] if white_castling else 0

            if white_a_side and msb(white_a_side) > msb(white_king_mask):
                white_a_side = 0
            if white_h_side and msb(white_h_side) < msb(white_king_mask):
                white_h_side = 0

            black_a_side = black_castling & -black_castling
            black_h_side = (
                BB_SQUARES[msb(black_castling)] if black_castling else BB_EMPTY
            )

            if black_a_side and msb(black_a_side) > msb(black_king_mask):
                black_a_side = 0
            if black_h_side and msb(black_h_side) < msb(black_king_mask):
                black_h_side = 0

            return black_a_side | black_h_side | white_a_side | white_h_side

    def _ep_skewered(self, king: int, capturer: int) -> bool:
        assert self.ep_square is not None
        last_double = self.ep_square + (-8 if self.turn == WHITE else 8)

        occupancy = (
            self.occupied & ~BB_SQUARES[last_double] & ~BB_SQUARES[capturer]
            | BB_SQUARES[self.ep_square]
        )

        horizontal_attackers = self.occupied_co[not self.turn] & (
            self.rooks | self.queens
        )
        if BB_RK_ATTACKS[king][BB_RK_MASKS[king] & occupancy] & horizontal_attackers:
            return True

        diagonal_attackers = self.occupied_co[not self.turn] & (
            self.bishops | self.queens
        )
        if BB_DIAG_ATTACKS[king][BB_DIAG_MASKS[king] & occupancy] & diagonal_attackers:
            return True

        return False

    def _slider_blockers(self, king: int) -> int:
        rooks_and_queens = self.rooks | self.queens
        bishops_and_queens = self.bishops | self.queens
        snipers = (
            (BB_RK_ATTACKS[king][0] & rooks_and_queens)
            | (BB_FL_ATTACKS[king][0] & rooks_and_queens)
            | (BB_DIAG_ATTACKS[king][0] & bishops_and_queens)
        )
        blockers = 0

        for sniper in scan_reversed(snipers & self.occupied_co[not self.turn]):
            b = between(king, sniper) & self.occupied

            if b and BB_SQUARES[msb(b)] == b:
                blockers |= b

        return blockers & self.occupied_co[self.turn]

    def _is_safe(self, king: int, blockers: int, move: Move) -> bool:
        if move.from_square == king:
            if self.is_castling(move):
                return True
            else:
                return not self.is_attacked_by(not self.turn, move.to_square)
        elif self.is_en_passant(move):
            return bool(
                self.pin_mask(self.turn, move.from_square) & BB_SQUARES[move.to_square]
                and not self._ep_skewered(king, move.from_square)
            )
        else:
            return bool(
                not blockers & BB_SQUARES[move.from_square]
                or ray(move.from_square, move.to_square) & BB_SQUARES[king]
            )

    def _generate_evasions(
        self,
        king: int,
        checkers: int,
        from_mask: int = BB_ALL,
        to_mask: int = BB_ALL,
    ):
        sliders = checkers & (self.bishops | self.rooks | self.queens)

        attacked = 0
        for checker in scan_reversed(sliders):
            attacked |= ray(king, checker) & ~BB_SQUARES[checker]

        if BB_SQUARES[king] & from_mask:
            for to_square in scan_reversed(
                BB_KING_ATTACKS[king]
                & ~self.occupied_co[self.turn]
                & ~attacked
                & to_mask
            ):
                yield Move(king, to_square)

        checker = msb(checkers)
        if BB_SQUARES[checker] == checkers:

            target = between(king, checker) | checkers

            yield from self.generate_pseudo_legal_moves(
                ~self.kings & from_mask, target & to_mask
            )

            if self.ep_square and not BB_SQUARES[self.ep_square] & target:
                last_double = self.ep_square + (-8 if self.turn == WHITE else 8)
                if last_double == checker:
                    yield from self.generate_pseudo_legal_ep(from_mask, to_mask)

    def generate_legal_moves(
        self, from_mask: int = BB_ALL, to_mask: int = BB_ALL
    ):
        king_mask = self.kings & self.occupied_co[self.turn]
        if king_mask:
            king = msb(king_mask)
            blockers = self._slider_blockers(king)
            checkers = self.attackers_mask(not self.turn, king)
            if checkers:
                for move in self._generate_evasions(king, checkers, from_mask, to_mask):
                    if self._is_safe(king, blockers, move):
                        yield move
            else:
                for move in self.generate_pseudo_legal_moves(from_mask, to_mask):
                    if self._is_safe(king, blockers, move):
                        yield move
        else:
            yield from self.generate_pseudo_legal_moves(from_mask, to_mask)

    def generate_castling_moves(
        self, from_mask: int = BB_ALL, to_mask: int = BB_ALL
    ):
        backrank = BB_RK_1 if self.turn == WHITE else BB_RK_8
        king = (
            self.occupied_co[self.turn]
            & self.kings
            & ~self.promoted
            & backrank
            & from_mask
        )
        king &= -king
        if not king:
            return

        bb_c = BB_FL_C & backrank
        bb_d = BB_FL_D & backrank
        bb_f = BB_FL_F & backrank
        bb_g = BB_FL_G & backrank

        for candidate in scan_reversed(
            self.clean_castling_rights() & backrank & to_mask
        ):
            rook = BB_SQUARES[candidate]

            a_side = rook < king
            king_to = bb_c if a_side else bb_g
            rook_to = bb_d if a_side else bb_f

            king_path = between(msb(king), msb(king_to))
            rook_path = between(candidate, msb(rook_to))

            if not (
                (self.occupied ^ king ^ rook)
                & (king_path | rook_path | king_to | rook_to)
                or self._attacked_for_king(king_path | king, self.occupied ^ king)
                or self._attacked_for_king(
                    king_to, self.occupied ^ king ^ rook ^ rook_to
                )
            ):
                yield self._from_chess960(self.chess960, msb(king), candidate)

    def _from_chess960(
        self,
        chess960: bool,
        from_square: int,
        to_square: int,
        promotion = None,
        drop = None,
    ) -> Move:
        if not chess960 and promotion is None and drop is None:
            if from_square == SQUARES_DICT["E1"] and self.kings & BB_DICT["BB_E1"]:
                if to_square == SQUARES_DICT["H1"]:
                    return Move(SQUARES_DICT["E1"], SQUARES_DICT["G1"])
                elif to_square == SQUARES_DICT["A1"]:
                    return Move(SQUARES_DICT["E1"], SQUARES_DICT["C1"])
            elif from_square == SQUARES_DICT["E8"] and self.kings & BB_DICT["BB_E8"]:
                if to_square == SQUARES_DICT["H8"]:
                    return Move(SQUARES_DICT["E8"], SQUARES_DICT["G8"])
                elif to_square == SQUARES_DICT["A8"]:
                    return Move(SQUARES_DICT["E8"], SQUARES_DICT["C8"])

        return Move(from_square, to_square, promotion, drop)

    def _to_chess960(self, move: Move) -> Move:
        if move.from_square == SQUARES_DICT["E1"] and self.kings & BB_DICT["BB_E1"]:
            if (
                move.to_square == SQUARES_DICT["G1"]
                and not self.rooks & BB_DICT["BB_G1"]
            ):
                return Move(SQUARES_DICT["E1"], SQUARES_DICT["H1"])
            elif (
                move.to_square == SQUARES_DICT["C1"]
                and not self.rooks & BB_DICT["BB_C1"]
            ):
                return Move(SQUARES_DICT["E1"], SQUARES_DICT["A1"])
        elif move.from_square == SQUARES_DICT["E8"] and self.kings & BB_DICT["BB_E8"]:
            if (
                move.to_square == SQUARES_DICT["G8"]
                and not self.rooks & BB_DICT["BB_G8"]
            ):
                return Move(SQUARES_DICT["E8"], SQUARES_DICT["H8"])
            elif (
                move.to_square == SQUARES_DICT["C8"]
                and not self.rooks & BB_DICT["BB_C8"]
            ):
                return Move(SQUARES_DICT["E8"], SQUARES_DICT["A8"])

        return move

class LegalMoveGenerator:
    def __init__(self, board: Board) -> None:
        self.board = board

    def __iter__(self):
        return self.board.generate_legal_moves()

class intSet:
    def __init__(self, squares=BB_EMPTY) -> None:
        self.mask: int = squares.__int__() & BB_ALL
        return

    def __iter__(self):
        return scan_forward(self.mask)

    def __len__(self) -> int:
        return popcount(self.mask)


def calc_heuristic(state: Board, isWhite: bool):
    if state.is_checkmate():
        return (state.turn * 2 - 1) * -float("inf")

    if (
        state.is_stalemate()
        or state.is_insufficient_material()
        or state.is_fivefold_repetition()
    ):
        return 0
    
    turn = "w" if isWhite else "b"
    return get_value(state.board_fen() + " " + turn)


def minimax(state, depth: int, alpha: float, beta: float, maximizingPlayer):
    global start_time, time_limit
    
    if ((time.time() - start_time) > time_limit) or (depth == 0):
        return calc_heuristic(state, maximizingPlayer), None

    best_move = None

    moves = list(state.legal_moves)

    # def move_value(move):
    #     return (
    #         state.is_capture(move)
    #         + 0.5 * state.gives_check(move)
    #         + 0.01 * random.random()
    #     )

    # moves.sort(key=move_value, reverse=True)

    max_value = -float("inf")
    min_value = float("inf")
    for move in moves:
        state.push(move)
        value, _ = minimax(state, depth - 1, alpha, beta, not maximizingPlayer)
        state.pop()
        if maximizingPlayer:
            if value > max_value:
                max_value = value
                best_move = move
            alpha = max(alpha, max_value)
        else:
            if value < min_value:
                min_value = value
                best_move = move
            beta = min(beta, min_value)

        if beta <= alpha:
            break
    return (max_value, best_move) if maximizingPlayer else (min_value, best_move)

start_time: int
time_limit: int

max_depth = 3

def chess_bot(obs):
    global start_time, time_limit, max_depth
    print(obs)
    game = Board(obs.board)
    legal_moves = get_move(obs.board).split()
    start_time = time.time()
    y = obs["remainingOverageTime"]
    time_limit = 0.09 if y > 2 else y/5
    if not legal_moves: return "resign"
    if y <= 0.1: return random.choice(legal_moves)
    
    if "e1g1" in legal_moves: return "e1g1"
    if "e1b1" in legal_moves: return "e1b1"
    if "e8g8" in legal_moves: return "e8g8"
    if "e8b8" in legal_moves: return "e8b8"
    
    _, move = minimax(
        game,
        depth=max_depth,
        alpha=-float("inf"),
        beta=float("inf"),
        maximizingPlayer=game.turn,
    )

    if move is None: move = random.choice(legal_moves)
    
    return str(move)
