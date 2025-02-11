from __future__ import annotations
import numpy as np
import random
import dataclasses
import typing
import time

from typing import (
    Callable,
    List,
    Dict,
    Iterable,
    Iterator,
    Optional,
    SupportsInt,
    Tuple,
    Union,
)

if typing.TYPE_CHECKING:
    from typing_extensions import Self, TypeAlias

Color: TypeAlias = bool
WHITE: Color = True
BLACK: Color = False
COLORS: List[Color] = [WHITE, BLACK]

PieceType: TypeAlias = int
PAWN: PieceType = 1
KNIGHT: PieceType = 2
BISHOP: PieceType = 3
ROOK: PieceType = 4
QUEEN: PieceType = 5
KING: PieceType = 6
PIECE_SYMBOLS = [None, "p", "n", "b", "r", "q", "k"]


def piece_symbol(tpe: PieceType) -> str:
    return typing.cast(str, PIECE_SYMBOLS[tpe])


FILE_NAMES = ["a", "b", "c", "d", "e", "f", "g", "h"]
RANK_NAMES = ["1", "2", "3", "4", "5", "6", "7", "8"]

Square: TypeAlias = int

SQUARES_DICT = {
    str(chr(65 + col)) + str(row): row * 8 + col
    for row in range(1, 9)
    for col in range(8)
}
SQUARES: List[Square] = list(range(64))
SQUARE_NAMES = [f + r for r in RANK_NAMES for f in FILE_NAMES]

def square_file(square: Square) -> int:
    return square & 7


def square_rank(square: Square) -> int:
    return square >> 3


def square_distance(a: Square, b: Square) -> int:
    return max(
        abs(square_file(a) - square_file(b)), abs(square_rank(a) - square_rank(b))
    )

def square_mirror(square: Square) -> Square:
    return square ^ 0x38


SQUARES_180: List[Square] = [square_mirror(sq) for sq in SQUARES]

Bitboard: TypeAlias = int
BB_EMPTY: Bitboard = 0
BB_ALL: Bitboard = 0xFFFF_FFFF_FFFF_FFFF

SQUARES_DICT: Dict[str, int] = {
    str(chr(65 + col)) + str(row): row * 8 + col
    for row in range(1, 9)
    for col in range(8)
}
BB_DICT = {"BB_" + str(square): 1 << index for square, index in SQUARES_DICT.items()}
BB_SQUARES: List[Bitboard] = [1 << sq for sq in SQUARES]

# BB_COR: Bitboard = (
#     BB_DICT["BB_A1"] | BB_DICT["BB_H1"] | BB_DICT["BB_A8"] | BB_DICT["BB_H8"]
# )

BB_LIGHT_SQUARES: Bitboard = 0x55AA_55AA_55AA_55AA
BB_DARK_SQUARES: Bitboard = 0xAA55_AA55_AA55_AA55

BB_FL_A: Bitboard = 0x0101_0101_0101_0101 << 0
BB_FL_B: Bitboard = 0x0101_0101_0101_0101 << 1
BB_FL_C: Bitboard = 0x0101_0101_0101_0101 << 2
BB_FL_D: Bitboard = 0x0101_0101_0101_0101 << 3
BB_FL_E: Bitboard = 0x0101_0101_0101_0101 << 4
BB_FL_F: Bitboard = 0x0101_0101_0101_0101 << 5
BB_FL_G: Bitboard = 0x0101_0101_0101_0101 << 6
BB_FL_H: Bitboard = 0x0101_0101_0101_0101 << 7
BB_FLS: List[Bitboard] = [
    BB_FL_A,
    BB_FL_B,
    BB_FL_C,
    BB_FL_D,
    BB_FL_E,
    BB_FL_F,
    BB_FL_G,
    BB_FL_H,
]

BB_RK_1: Bitboard = 0xFF << (8 * 0)
BB_RK_2: Bitboard = 0xFF << (8 * 1)
BB_RK_3: Bitboard = 0xFF << (8 * 2)
BB_RK_4: Bitboard = 0xFF << (8 * 3)
BB_RK_5: Bitboard = 0xFF << (8 * 4)
BB_RK_6: Bitboard = 0xFF << (8 * 5)
BB_RK_7: Bitboard = 0xFF << (8 * 6)
BB_RK_8: Bitboard = 0xFF << (8 * 7)
BB_RKS: List[Bitboard] = [
    BB_RK_1,
    BB_RK_2,
    BB_RK_3,
    BB_RK_4,
    BB_RK_5,
    BB_RK_6,
    BB_RK_7,
    BB_RK_8,
]

BB_BACKRANKS: Bitboard = BB_RK_1 | BB_RK_8


def lsb(bb: Bitboard) -> int:
    return (bb & -bb).bit_length() - 1


def scan_forward(bb: Bitboard) -> Iterator[Square]:
    while bb:
        r = bb & -bb
        yield r.bit_length() - 1
        bb ^= r


def msb(bb: Bitboard) -> int:
    return bb.bit_length() - 1


def scan_reversed(bb: Bitboard) -> Iterator[Square]:
    while bb:
        r = bb.bit_length() - 1
        yield r
        bb ^= BB_SQUARES[r]


popcount: Callable[[Bitboard], int] = getattr(
    int, "bit_count", lambda bb: bin(bb).count("1")
)


def _sliding_attacks(
    square: Square, occupied: Bitboard, deltas: Iterable[int]
) -> Bitboard:
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


def _step_attacks(square: Square, deltas: Iterable[int]) -> Bitboard:
    return _sliding_attacks(square, BB_ALL, deltas)


BB_KNIGHT_ATTACKS: List[Bitboard] = [
    _step_attacks(sq, [17, 15, 10, 6, -17, -15, -10, -6]) for sq in SQUARES
]
BB_KING_ATTACKS: List[Bitboard] = [
    _step_attacks(sq, [9, 8, 7, 1, -9, -8, -7, -1]) for sq in SQUARES
]
BB_PAWN_ATTACKS: List[List[Bitboard]] = [
    [_step_attacks(sq, deltas) for sq in SQUARES] for deltas in [[-7, -9], [7, 9]]
]


def _edges(square: Square) -> Bitboard:
    return ((BB_RK_1 | BB_RK_8) & ~BB_RKS[square_rank(square)]) | (
        (BB_FL_A | BB_FL_H) & ~BB_FLS[square_file(square)]
    )


def _carry_rippler(mask: Bitboard) -> Iterator[Bitboard]:
    subset = BB_EMPTY
    while True:
        yield subset
        subset = (subset - mask) & mask
        if not subset:
            break


def _attack_table(
    deltas: List[int],
) -> Tuple[List[Bitboard], List[Dict[Bitboard, Bitboard]]]:
    mask_table: List[Bitboard] = []
    attack_table: List[Dict[Bitboard, Bitboard]] = []

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


def _rays() -> List[List[Bitboard]]:
    rays: List[List[Bitboard]] = []
    for a, bb_a in enumerate(BB_SQUARES):
        rays_row: List[Bitboard] = []
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


def ray(a: Square, b: Square) -> Bitboard:
    return BB_RAYS[a][b]


def between(a: Square, b: Square) -> Bitboard:
    bb = BB_RAYS[a][b] & ((BB_ALL << a) ^ (BB_ALL << b))
    return bb & (bb - 1)


@dataclasses.dataclass
class Piece:
    tpe: PieceType
    color: Color

#     def __hash__(self) -> int:
#         return self.tpe + (-1 if self.color else 5)

#     def __repr__(self) -> str:
#         return "Piece.from_symbol(" + self.symbol() + ")"

#     def __str__(self) -> str:
#         return self.symbol()

    @classmethod
    def from_symbol(cls, symbol: str) -> Piece:

        return cls(PIECE_SYMBOLS.index(symbol.lower()), symbol.isupper())


@dataclasses.dataclass(unsafe_hash=True)
class Move:
    from_square: Square
    to_square: Square
    promotion: Optional[PieceType] = None
    drop: Optional[PieceType] = None

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

#     def xboard(self) -> str:
#         return self.uci() if self else "@@@@"

#     def __bool__(self) -> bool:
#         return bool(self.from_square or self.to_square or self.promotion or self.drop)

#     def __repr__(self) -> str:
#         return "Move.from_uci(" + self.uci() + ")"

    def __str__(self) -> str:
        return self.uci()

#     @classmethod
#     def null(cls) -> Move:

#         return cls(0, 0)


# BaseBoardT = TypeVar("BaseBoardT", bound="BaseBoard")


class BaseBoard:
    def __init__(self, board_fen: str) -> None:
        self.occupied_co = [BB_EMPTY, BB_EMPTY]
        #         if board_fen is None:
        #             self._clear_board()
        #         else:
        #             self._set_board_fen(board_fen)

        #     def _reset_board(self) -> None:
        #         self.pawns = BB_RK_2 | BB_RK_7
        #         self.knights = (
        #             BB_DICT["BB_B1"] | BB_DICT["BB_G1"] | BB_DICT["BB_B8"] | BB_DICT["BB_G8"]
        #         )
        #         self.bishops = (
        #             BB_DICT["BB_C1"] | BB_DICT["BB_F1"] | BB_DICT["BB_C8"] | BB_DICT["BB_F8"]
        #         )
        #         self.rooks = BB_COR
        #         self.queens = BB_DICT["BB_D1"] | BB_DICT["BB_D8"]
        #         self.kings = BB_DICT["BB_E1"] | BB_DICT["BB_E8"]

        #         self.promoted = BB_EMPTY

        #         self.occupied_co[WHITE] = BB_RK_1 | BB_RK_2
        #         self.occupied_co[BLACK] = BB_RK_7 | BB_RK_8
        #         self.occupied = BB_RK_1 | BB_RK_2 | BB_RK_7 | BB_RK_8

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

    #     def clear_board(self) -> None:
    #         self._clear_board()

    def pieces_mask(self, tpe: PieceType, color: Color) -> Bitboard:
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

    def pieces(self, tpe: PieceType, color: Color) -> SquareSet:
        return SquareSet(self.pieces_mask(tpe, color))

    #     def piece_at(self, square: Square) -> Optional[Piece]:

    #         tpe = self.tpe_at(square)
    #         if tpe:
    #             mask = BB_SQUARES[square]
    #             color = bool(self.occupied_co[WHITE] & mask)
    #             return Piece(tpe, color)
    #         else:
    #             return None

    def tpe_at(self, square: Square) -> Optional[PieceType]:
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

    #     def color_at(self, square: Square) -> Optional[Color]:

    #         mask = BB_SQUARES[square]
    #         if self.occupied_co[WHITE] & mask:
    #             return WHITE
    #         elif self.occupied_co[BLACK] & mask:
    #             return BLACK
    #         else:
    #             return None

    def king(self, color: Color) -> Optional[Square]:
        king_mask = self.occupied_co[color] & self.kings & ~self.promoted
        return msb(king_mask) if king_mask else None

    def attacks_mask(self, square: Square) -> Bitboard:
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

    #     def attacks(self, square: Square) -> SquareSet:

    #         return SquareSet(self.attacks_mask(square))

    def attackers_mask(
        self, color: Color, square: Square, occupied: Optional[Bitboard] = None
    ) -> Bitboard:
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

    def is_attacked_by(
        self, color: Color, square: Square, occupied: Optional[IntoSquareSet] = None
    ) -> bool:

        return bool(
            self.attackers_mask(
                color, square, None if occupied is None else SquareSet(occupied).mask
            )
        )

    #     def attackers(
    #         self, color: Color, square: Square, occupied: Optional[IntoSquareSet] = None
    #     ) -> SquareSet:

    #         return SquareSet(
    #             self.attackers_mask(
    #                 color, square, None if occupied is None else SquareSet(occupied).mask
    #             )
    #         )

    def pin_mask(self, color: Color, square: Square) -> Bitboard:
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

    #     def pin(self, color: Color, square: Square) -> SquareSet:

    #         return SquareSet(self.pin_mask(color, square))

    #     def is_pinned(self, color: Color, square: Square) -> bool:

    #         return self.pin_mask(color, square) != BB_ALL

    def _remove_piece_at(self, square: Square) -> Optional[PieceType]:
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

    #     def remove_piece_at(self, square: Square) -> Optional[Piece]:

    #         color = bool(self.occupied_co[WHITE] & BB_SQUARES[square])
    #         tpe = self._remove_piece_at(square)
    #         return Piece(tpe, color) if tpe else None

    def _set_piece_at(
        self,
        square: Square,
        tpe: PieceType,
        color: Color,
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

    #     def set_piece_at(
    #         self, square: Square, piece: Optional[Piece], promoted: bool = False
    #     ) -> None:

    #         if piece is None:
    #             self._remove_piece_at(square)
    #         else:
    #             self._set_piece_at(square, piece.tpe, piece.color, promoted)

    #     def board_fen(self, *, promoted: Optional[bool] = False) -> str:

    #         builder: List[str] = []
    #         empty = 0

    #         for square in SQUARES_180:
    #             piece = self.piece_at(square)

    #             if not piece:
    #                 empty += 1
    #             else:
    #                 if empty:
    #                     builder.append(str(empty))
    #                     empty = 0
    #                 builder.append(piece.symbol())
    #                 if promoted and BB_SQUARES[square] & self.promoted:
    #                     builder.append("~")

    #             if BB_SQUARES[square] & BB_FL_H:
    #                 if empty:
    #                     builder.append(str(empty))
    #                     empty = 0

    #                 if square != SQUARES_DICT["H1"]:
    #                     builder.append("/")

    #         return "".join(builder)

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
                piece = Piece.from_symbol(c)
                self._set_piece_at(SQUARES_180[square_index], piece.tpe, piece.color)
                square_index += 1
            elif c == "~":
                self.promoted |= BB_SQUARES[SQUARES_180[square_index - 1]]


#     def set_board_fen(self, fen: str) -> None:

#         self._set_board_fen(fen)

#     def piece_map(self, *, mask: Bitboard = BB_ALL) -> Dict[Square, Piece]:

#         result: Dict[Square, Piece] = {}
#         for square in scan_reversed(self.occupied & mask):
#             result[square] = typing.cast(Piece, self.piece_at(square))
#         return result

#     def _set_piece_map(self, pieces: Mapping[Square, Piece]) -> None:
#         self._clear_board()
#         for square, piece in pieces.items():
#             self._set_piece_at(square, piece.tpe, piece.color)

#     def set_piece_map(self, pieces: Mapping[Square, Piece]) -> None:

#         self._set_piece_map(pieces)

#     def _set_chess960_pos(self, scharnagl: int) -> None:
#         n, bw = divmod(scharnagl, 4)
#         n, bb = divmod(n, 4)
#         n, q = divmod(n, 6)

#         for n1 in range(0, 4):
#             n2 = n + (3 - n1) * (4 - n1) // 2 - 5
#             if n1 < n2 and 1 <= n2 <= 4:
#                 break

#         bw_file = bw * 2 + 1
#         bb_file = bb * 2
#         self.bishops = (BB_FLS[bw_file] | BB_FLS[bb_file]) & BB_BACKRANKS

#         q_file = q
#         q_file += int(min(bw_file, bb_file) <= q_file)
#         q_file += int(max(bw_file, bb_file) <= q_file)
#         self.queens = BB_FLS[q_file] & BB_BACKRANKS

#         used = [bw_file, bb_file, q_file]

#         self.knights = BB_EMPTY
#         for i in range(0, 8):
#             if i not in used:
#                 if n1 == 0 or n2 == 0:
#                     self.knights |= BB_FLS[i] & BB_BACKRANKS
#                     used.append(i)
#                 n1 -= 1
#                 n2 -= 1

#         for i in range(0, 8):
#             if i not in used:
#                 self.rooks = BB_FLS[i] & BB_BACKRANKS
#                 used.append(i)
#                 break
#         for i in range(1, 8):
#             if i not in used:
#                 self.kings = BB_FLS[i] & BB_BACKRANKS
#                 used.append(i)
#                 break
#         for i in range(2, 8):
#             if i not in used:
#                 self.rooks |= BB_FLS[i] & BB_BACKRANKS
#                 break

#         self.pawns = BB_RK_2 | BB_RK_7
#         self.occupied_co[WHITE] = BB_RK_1 | BB_RK_2
#         self.occupied_co[BLACK] = BB_RK_7 | BB_RK_8
#         self.occupied = BB_RK_1 | BB_RK_2 | BB_RK_7 | BB_RK_8
#         self.promoted = BB_EMPTY

#     def set_chess960_pos(self, scharnagl: int) -> None:

#         self._set_chess960_pos(scharnagl)

#     def chess960_pos(self) -> Optional[int]:

#         if self.occupied_co[WHITE] != BB_RK_1 | BB_RK_2:
#             return None
#         if self.occupied_co[BLACK] != BB_RK_7 | BB_RK_8:
#             return None
#         if self.pawns != BB_RK_2 | BB_RK_7:
#             return None
#         if self.promoted:
#             return None

#         brnqk = [self.bishops, self.rooks, self.knights, self.queens, self.kings]
#         if [popcount(pieces) for pieces in brnqk] != [4, 4, 4, 2, 2]:
#             return None

#         if any((BB_RK_1 & pieces) << 56 != BB_RK_8 & pieces for pieces in brnqk):
#             return None

#         x = self.bishops & (2 + 8 + 32 + 128)
#         if not x:
#             return None
#         bs1 = (lsb(x) - 1) // 2
#         cc_pos = bs1
#         x = self.bishops & (1 + 4 + 16 + 64)
#         if not x:
#             return None
#         bs2 = lsb(x) * 2
#         cc_pos += bs2

#         q = 0
#         qf = False
#         n0 = 0
#         n1 = 0
#         n0f = False
#         n1f = False
#         rf = 0
#         n0s = [0, 4, 7, 9]
#         for square in range(SQUARES_DICT["A1"], SQUARES_DICT["H1"] + 1):
#             bb = BB_SQUARES[square]
#             if bb & self.queens:
#                 qf = True
#             elif bb & self.rooks or bb & self.kings:
#                 if bb & self.kings:
#                     if rf != 1:
#                         return None
#                 else:
#                     rf += 1

#                 if not qf:
#                     q += 1

#                 if not n0f:
#                     n0 += 1
#                 elif not n1f:
#                     n1 += 1
#             elif bb & self.knights:
#                 if not qf:
#                     q += 1

#                 if not n0f:
#                     n0f = True
#                 elif not n1f:
#                     n1f = True

#         if n0 < 4 and n1f and qf:
#             cc_pos += q * 16
#             krn = n0s[n0] + n1
#             cc_pos += krn * 96
#             return cc_pos
#         else:
#             return None

#     def __repr__(self) -> str:
#         return (type(self).__name__) + "(" + (self.board_fen()) + ")"

#     def __str__(self) -> str:
#         builder: List[str] = []

#         for square in SQUARES_180:
#             piece = self.piece_at(square)

#             if piece:
#                 builder.append(piece.symbol())
#             else:
#                 builder.append(".")

#             if BB_SQUARES[square] & BB_FL_H:
#                 if square != SQUARES_DICT["H1"]:
#                     builder.append("\n")
#             else:
#                 builder.append(" ")

#         return "".join(builder)

#     def unicode(
#         self,
#         *,
#         invert_color: bool = False,
#         borders: bool = False,
#         empty_square: str = "⭘",
#         orientation: Color = WHITE,
#     ) -> str:

#         builder: List[str] = []
#         for rank_index in range(7, -1, -1) if orientation else range(8):
#             if borders:
#                 builder.append("  ")
#                 builder.append("-" * 17)
#                 builder.append("\n")

#                 builder.append(RANK_NAMES[rank_index])
#                 builder.append(" ")

#             for i, file_index in enumerate(
#                 range(8) if orientation else range(7, -1, -1)
#             ):
#                 square_index = square(file_index, rank_index)

#                 if borders:
#                     builder.append("|")
#                 elif i > 0:
#                     builder.append(" ")

#                 piece = self.piece_at(square_index)

#                 if piece:
#                     builder.append(piece.unicode_symbol(invert_color=invert_color))
#                 else:
#                     builder.append(empty_square)

#             if borders:
#                 builder.append("|")

#             if borders or (rank_index > 0 if orientation else rank_index < 7):
#                 builder.append("\n")

#         if borders:
#             builder.append("  ")
#             builder.append("-" * 17)
#             builder.append("\n")
#             letters = "a b c d e f g h" if orientation else "h g f e d c b a"
#             builder.append("   " + letters)

#         return "".join(builder)

#     def _repr_svg_(self) -> str:
#         import chess.svg

#         return chess.svg.board(board=self, size=400)

#     def __eq__(self, board: object) -> bool:
#         if isinstance(board, BaseBoard):
#             return (
#                 self.occupied == board.occupied
#                 and self.occupied_co[WHITE] == board.occupied_co[WHITE]
#                 and self.pawns == board.pawns
#                 and self.knights == board.knights
#                 and self.bishops == board.bishops
#                 and self.rooks == board.rooks
#                 and self.queens == board.queens
#                 and self.kings == board.kings
#             )
#         else:
#             return NotImplemented

#     def apply_transform(self, f: Callable[[Bitboard], Bitboard]) -> None:
#         self.pawns = f(self.pawns)
#         self.knights = f(self.knights)
#         self.bishops = f(self.bishops)
#         self.rooks = f(self.rooks)
#         self.queens = f(self.queens)
#         self.kings = f(self.kings)

#         self.occupied_co[WHITE] = f(self.occupied_co[WHITE])
#         self.occupied_co[BLACK] = f(self.occupied_co[BLACK])
#         self.occupied = f(self.occupied)
#         self.promoted = f(self.promoted)

#     def transform(self, f: Callable[[Bitboard], Bitboard]) -> Self:

#         board = self.copy()
#         board.apply_transform(f)
#         return board

#     # def apply_mirror(self) -> None:
#     #     self.apply_transform(flip_vertical)
#     #     self.occupied_co[WHITE], self.occupied_co[BLACK] = (
#     #         self.occupied_co[BLACK],
#     #         self.occupied_co[WHITE],
#     #     )

#     # def mirror(self) -> Self:

#     #     board = self.copy()
#     #     board.apply_mirror()
#     #     return board

#     def copy(self) -> Self:

#         board = type(self)(None)

#         board.pawns = self.pawns
#         board.knights = self.knights
#         board.bishops = self.bishops
#         board.rooks = self.rooks
#         board.queens = self.queens
#         board.kings = self.kings

#         board.occupied_co[WHITE] = self.occupied_co[WHITE]
#         board.occupied_co[BLACK] = self.occupied_co[BLACK]
#         board.occupied = self.occupied
#         board.promoted = self.promoted

#         return board

#     def __copy__(self) -> Self:
#         return self.copy()

#     def __deepcopy__(self, memo: Dict[int, object]) -> Self:
#         board = self.copy()
#         memo[id(self)] = board
#         return board

#     @classmethod
#     def empty(cls: Type[BaseBoardT]) -> BaseBoardT:

#         return cls(None)

#     @classmethod
#     def from_chess960_pos(cls: Type[BaseBoardT], scharnagl: int) -> BaseBoardT:

#         board = cls.empty()
#         board.set_chess960_pos(scharnagl)
#         return board


# BoardT = TypeVar("BoardT", bound="Board")


class _BoardState:
    def __init__(self, board: Board) -> None:
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

    def restore(self, board: Board) -> None:
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
    #     aliases: ClassVar[List[str]] = [
    #         "Standard",
    #         "Chess",
    #         "Classical",
    #         "Normal",
    #         "Illegal",
    #         "From Position",
    #     ]
    #     uci_variant: ClassVar[Optional[str]] = "chess"
    #     xboard_variant: ClassVar[Optional[str]] = "normal"

    #     tbw_suffix: ClassVar[Optional[str]] = ".rtbw"
    #     tbz_suffix: ClassVar[Optional[str]] = ".rtbz"
    #     tbw_magic: ClassVar[Optional[bytes]] = b"\x71\xe8\x23\x5d"
    #     tbz_magic: ClassVar[Optional[bytes]] = b"\xd7\x66\x0c\xa5"
    #     pawnless_tbw_suffix: ClassVar[Optional[str]] = None
    #     pawnless_tbz_suffix: ClassVar[Optional[str]] = None
    #     pawnless_tbw_magic: ClassVar[Optional[bytes]] = None
    #     pawnless_tbz_magic: ClassVar[Optional[bytes]] = None
    #     connected_kings: ClassVar[bool] = False
    #     one_king: ClassVar[bool] = True
    #     captures_compulsory: ClassVar[bool] = False

    #     turn: Color

    #     castling_rights: Bitboard

    #     ep_square: Optional[Square]

    #     fullmove_number: int

    #     halfmove_clock: int

    #     promoted: Bitboard

    #     chess960: bool

    #     move_stack: List[Move]

    def __init__(self, fen: str, *, chess960: bool = False) -> None:
        BaseBoard.__init__(self, None)

        self.chess960 = chess960

        self.ep_square = None
        self.move_stack = []
        self._stack: List[_BoardState] = []

        if fen is None:
            self.clear()
        else:
            self.set_fen(fen)

    @property
    def legal_moves(self) -> LegalMoveGenerator:
        return LegalMoveGenerator(self)

    #     def reset(self) -> None:
    #         self.turn = WHITE
    #         self.castling_rights = BB_COR
    #         self.ep_square = None
    #         self.halfmove_clock = 0
    #         self.fullmove_number = 1

    #         self.reset_board()

    #     def reset_board(self) -> None:
    #         super().reset_board()
    #         self.clear_stack()

    #     def clear(self) -> None:

    #         self.turn = WHITE
    #         self.castling_rights = BB_EMPTY
    #         self.ep_square = None
    #         self.halfmove_clock = 0
    #         self.fullmove_number = 1

    #         self.clear_board()

    #     def clear_board(self) -> None:
    #         super().clear_board()
    #         self.clear_stack()

    def clear_stack(self) -> None:
        self.move_stack.clear()
        self._stack.clear()

    #     def root(self) -> Self:
    #         if self._stack:
    #             board = type(self)(None, chess960=self.chess960)
    #             self._stack[0].restore(board)
    #             return board
    #         else:
    #             return self.copy(stack=False)

    #     def ply(self) -> int:
    #         return 2 * (self.fullmove_number - 1) + (self.turn == BLACK)

    #     def remove_piece_at(self, square: Square) -> Optional[Piece]:
    #         piece = super().remove_piece_at(square)
    #         self.clear_stack()
    #         return piece

    #     def set_piece_at(
    #         self, square: Square, piece: Optional[Piece], promoted: bool = False
    #     ) -> None:
    #         super().set_piece_at(square, piece, promoted=promoted)
    #         self.clear_stack()

    def generate_pseudo_legal_moves(
        self, from_mask: Bitboard = BB_ALL, to_mask: Bitboard = BB_ALL
    ) -> Iterator[Move]:
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
        self, from_mask: Bitboard = BB_ALL, to_mask: Bitboard = BB_ALL
    ) -> Iterator[Move]:
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

    #     def generate_pseudo_legal_captures(
    #         self, from_mask: Bitboard = BB_ALL, to_mask: Bitboard = BB_ALL
    #     ) -> Iterator[Move]:
    #         return itertools.chain(
    #             self.generate_pseudo_legal_moves(
    #                 from_mask, to_mask & self.occupied_co[not self.turn]
    #             ),
    #             self.generate_pseudo_legal_ep(from_mask, to_mask),
    #         )

    def checkers_mask(self) -> Bitboard:
        king = self.king(self.turn)
        return BB_EMPTY if king is None else self.attackers_mask(not self.turn, king)

    #     def checkers(self) -> SquareSet:
    #         return SquareSet(self.checkers_mask())

    def is_check(self) -> bool:
        return bool(self.checkers_mask())

    def gives_check(self, move: Move) -> bool:
        self.push(move)
        try:
            return self.is_check()
        finally:
            self.pop()

    #     def is_into_check(self, move: Move) -> bool:
    #         king = self.king(self.turn)
    #         if king is None:
    #             return False

    #         checkers = self.attackers_mask(not self.turn, king)
    #         if checkers and move not in self._generate_evasions(
    #             king, checkers, BB_SQUARES[move.from_square], BB_SQUARES[move.to_square]
    #         ):
    #             return True

    #         return not self._is_safe(king, self._slider_blockers(king), move)

    #     def was_into_check(self) -> bool:
    #         king = self.king(not self.turn)
    #         return king is not None and self.is_attacked_by(self.turn, king)

    #     def is_pseudo_legal(self, move: Move) -> bool:

    #         if not move:
    #             return False

    #         if move.drop:
    #             return False

    #         piece = self.tpe_at(move.from_square)
    #         if not piece:
    #             return False

    #         from_mask = BB_SQUARES[move.from_square]
    #         to_mask = BB_SQUARES[move.to_square]

    #         if not self.occupied_co[self.turn] & from_mask:
    #             return False

    #         if move.promotion:
    #             if piece != PAWN:
    #                 return False

    #             if self.turn == WHITE and square_rank(move.to_square) != 7:
    #                 return False
    #             elif self.turn == BLACK and square_rank(move.to_square) != 0:
    #                 return False

    #         if piece == KING:
    #             move = self._from_chess960(self.chess960, move.from_square, move.to_square)
    #             if move in self.generate_castling_moves():
    #                 return True

    #         if self.occupied_co[self.turn] & to_mask:
    #             return False

    #         if piece == PAWN:
    #             return move in self.generate_pseudo_legal_moves(from_mask, to_mask)

    #         return bool(self.attacks_mask(move.from_square) & to_mask)

    #     def is_legal(self, move: Move) -> bool:
    #         return (
    #             and self.is_pseudo_legal(move)
    #             and not self.is_into_check(move)
    #         )

    #     def is_variant_end(self) -> bool:
    #         return False

    #     def is_variant_loss(self) -> bool:
    #         return False

    #     def is_variant_win(self) -> bool:

    #         return False

    #     def is_variant_draw(self) -> bool:

    #         return False

    #     def is_game_over(self, *, claim_draw: bool = False) -> bool:
    #         return self.outcome(claim_draw=claim_draw) is not None

    #     def result(self, *, claim_draw: bool = False) -> str:
    #         outcome = self.outcome(claim_draw=claim_draw)
    #         return outcome.result() if outcome else "*"

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

    def has_insufficient_material(self, color: Color) -> bool:
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

    #     def _is_halfmoves(self, n: int) -> bool:
    #         return self.halfmove_clock >= n and any(self.generate_legal_moves())

    #     def is_seventyfive_moves(self) -> bool:

    #         return self._is_halfmoves(150)

    def is_fivefold_repetition(self) -> bool:
        return self.is_repetition(5)

    #     def can_claim_draw(self) -> bool:

    #         return self.can_claim_fifty_moves() or self.can_claim_threefold_repetition()

    #     def is_fifty_moves(self) -> bool:

    #         return self._is_halfmoves(100)

    #     def can_claim_fifty_moves(self) -> bool:

    #         if self.is_fifty_moves():
    #             return True

    #         if self.halfmove_clock >= 99:
    #             for move in self.generate_legal_moves():
    #                 if not self.is_zeroing(move):
    #                     self.push(move)
    #                     try:
    #                         if self.is_fifty_moves():
    #                             return True
    #                     finally:
    #                         self.pop()

    #         return False

    #     def can_claim_threefold_repetition(self) -> bool:

    #         transposition_key = self._transposition_key()
    #         transpositions: Counter[Hashable] = collections.Counter()
    #         transpositions.update((transposition_key,))

    #         switchyard: List[Move] = []
    #         while self.move_stack:
    #             move = self.pop()
    #             switchyard.append(move)

    #             if self.is_irreversible(move):
    #                 break

    #             transpositions.update((self._transposition_key(),))

    #         while switchyard:
    #             self.push(switchyard.pop())

    #         if transpositions[transposition_key] >= 3:
    #             return True

    #         for move in self.generate_legal_moves():
    #             self.push(move)
    #             try:
    #                 if transpositions[self._transposition_key()] >= 2:
    #                     return True
    #             finally:
    #                 self.pop()

    #         return False

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
        switchyard: List[Move] = []

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

    def _push_capture(
        self,
        move: Move,
        capture_square: Square,
        tpe: PieceType,
        was_promoted: bool,
    ) -> None:
        pass

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
            was_promoted = bool(self.promoted & to_bb)
            self._set_piece_at(move.to_square, tpe, self.turn, promoted)

            if captured_tpe:
                self._push_capture(move, capture_square, captured_tpe, was_promoted)

        self.turn = not self.turn

    def pop(self) -> Move:
        move = self.move_stack.pop()
        self._stack.pop().restore(self)
        return move

    #     def peek(self) -> Move:

    #         return self.move_stack[-1]

    #     def find_move(
    #         self,
    #         from_square: Square,
    #         to_square: Square,
    #         promotion: Optional[PieceType] = None,
    #     ) -> Move:

    #         if (
    #             promotion is None
    #             and self.pawns & BB_SQUARES[from_square]
    #             and BB_SQUARES[to_square] & BB_BACKRANKS
    #         ):
    #             promotion = QUEEN

    #         move = self._from_chess960(self.chess960, from_square, to_square, promotion)

    #         return move

    #     def castling_shredder_fen(self) -> str:
    #         castling_rights = self.clean_castling_rights()
    #         if not castling_rights:
    #             return "-"

    #         builder: List[str] = []

    #         for square in scan_reversed(castling_rights & BB_RK_1):
    #             builder.append(FILE_NAMES[square_file(square)].upper())

    #         for square in scan_reversed(castling_rights & BB_RK_8):
    #             builder.append(FILE_NAMES[square_file(square)])

    #         return "".join(builder)

    #     def castling_xfen(self) -> str:
    #         builder: List[str] = []

    #         for color in COLORS:
    #             king = self.king(color)
    #             if king is None:
    #                 continue

    #             king_file = square_file(king)
    #             backrank = BB_RK_1 if color == WHITE else BB_RK_8

    #             for rook_square in scan_reversed(self.clean_castling_rights() & backrank):
    #                 rook_file = square_file(rook_square)
    #                 a_side = rook_file < king_file

    #                 other_rooks = (
    #                     self.occupied_co[color]
    #                     & self.rooks
    #                     & backrank
    #                     & ~BB_SQUARES[rook_square]
    #                 )

    #                 if any(
    #                     (square_file(other) < rook_file) == a_side
    #                     for other in scan_reversed(other_rooks)
    #                 ):
    #                     ch = FILE_NAMES[rook_file]
    #                 else:
    #                     ch = "q" if a_side else "k"

    #                 builder.append(ch.upper() if color == WHITE else ch)

    #         if builder:
    #             return "".join(builder)
    #         else:
    #             return "-"

    #     def has_pseudo_legal_en_passant(self) -> bool:

    #         return self.ep_square is not None and any(self.generate_pseudo_legal_ep())

    #     def has_legal_en_passant(self) -> bool:

    #         return self.ep_square is not None and any(self.generate_legal_ep())

    #     def fen(
    #         self,
    #         *,
    #         shredder: bool = False,
    #         en_passant: EnPassantSpec = "legal",
    #         promoted: Optional[bool] = None,
    #     ) -> str:

    #         return " ".join(
    #             [
    #                 self.epd(shredder=shredder, en_passant=en_passant, promoted=promoted),
    #                 str(self.halfmove_clock),
    #                 str(self.fullmove_number),
    #             ]
    #         )

    #     def shredder_fen(
    #         self, *, en_passant: EnPassantSpec = "legal", promoted: Optional[bool] = None
    #     ) -> str:
    #         return " ".join(
    #             [
    #                 self.epd(shredder=True, en_passant=en_passant, promoted=promoted),
    #                 str(self.halfmove_clock),
    #                 str(self.fullmove_number),
    #             ]
    #         )

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

#     def set_castling_fen(self, castling_fen: str) -> None:
#         self._set_castling_fen(castling_fen)
#         self.clear_stack()

#     def set_board_fen(self, fen: str) -> None:
#         super().set_board_fen(fen)
#         self.clear_stack()

#     def set_piece_map(self, pieces: Mapping[Square, Piece]) -> None:
#         super().set_piece_map(pieces)
#         self.clear_stack()

#     def set_chess960_pos(self, scharnagl: int) -> None:
#         super().set_chess960_pos(scharnagl)
#         self.chess960 = True
#         self.turn = WHITE
#         self.castling_rights = self.rooks
#         self.ep_square = None
#         self.halfmove_clock = 0
#         self.fullmove_number = 1

#         self.clear_stack()

#     def chess960_pos(
#         self,
#         *,
#         ignore_turn: bool = False,
#         ignore_castling: bool = False,
#         ignore_counters: bool = True,
#     ) -> Optional[int]:

#         if self.ep_square:
#             return None

#         if not ignore_turn:
#             if self.turn != WHITE:
#                 return None

#         if not ignore_castling:
#             if self.clean_castling_rights() != self.rooks:
#                 return None

#         if not ignore_counters:
#             if self.fullmove_number != 1 or self.halfmove_clock != 0:
#                 return None

#         return super().chess960_pos()

#     def san(self, move: Move) -> str:

#         return self._algebraic(move)

#     def lan(self, move: Move) -> str:

#         return self._algebraic(move, isLong=True)

#     def san_and_push(self, move: Move) -> str:
#         return self._algebraic_and_push(move)

#     def _algebraic(self, move: Move, *, isLong: bool = False) -> str:
#         san = self._algebraic_and_push(move, isLong=isLong)
#         self.pop()
#         return san

#     def _algebraic_and_push(self, move: Move, *, isLong: bool = False) -> str:
#         san = self._algebraic_without_suffix(move, isLong=isLong)

#         self.push(move)
#         is_check = self.is_check()
#         is_checkmate = (
#             (is_check and self.is_checkmate())
#             or self.is_variant_loss()
#             or self.is_variant_win()
#         )

#         if is_checkmate and move:
#             return san + "#"
#         elif is_check and move:
#             return san + "+"
#         else:
#             return san

#     def _algebraic_without_suffix(self, move: Move, *, isLong: bool = False) -> str:

#         if not move:
#             return "--"

#         if move.drop:
#             san = ""
#             if move.drop != PAWN:
#                 san = piece_symbol(move.drop).upper()
#             san += "@" + SQUARE_NAMES[move.to_square]
#             return san

#         if self.is_castling(move):
#             if square_file(move.to_square) < square_file(move.from_square):
#                 return "O-O-O"
#             else:
#                 return "O-O"

#         tpe = self.tpe_at(move.from_square)
#         capture = self.is_capture(move)

#         if tpe == PAWN:
#             san = ""
#         else:
#             san = piece_symbol(tpe).upper()

#         if isLong:
#             san += SQUARE_NAMES[move.from_square]
#         elif tpe != PAWN:

#             others = 0
#             from_mask = self.pieces_mask(tpe, self.turn)
#             from_mask &= ~BB_SQUARES[move.from_square]
#             to_mask = BB_SQUARES[move.to_square]
#             for candidate in self.generate_legal_moves(from_mask, to_mask):
#                 others |= BB_SQUARES[candidate.from_square]

#             if others:
#                 row, column = False, False

#                 if others & BB_RKS[square_rank(move.from_square)]:
#                     column = True

#                 if others & BB_FLS[square_file(move.from_square)]:
#                     row = True
#                 else:
#                     column = True

#                 if column:
#                     san += FILE_NAMES[square_file(move.from_square)]
#                 if row:
#                     san += RANK_NAMES[square_rank(move.from_square)]
#         elif capture:
#             san += FILE_NAMES[square_file(move.from_square)]

#         if capture:
#             san += "x"
#         elif isLong:
#             san += "-"

#         san += SQUARE_NAMES[move.to_square]

#         if move.promotion:
#             san += "=" + piece_symbol(move.promotion).upper()

#         return san

#     def variation_san(self, variation: Iterable[Move]) -> str:

#         board = self.copy(stack=False)
#         san: List[str] = []
#         for move in variation:
#             if board.turn == WHITE:
#                 san.append((board.fullmove_number) + "." + (board.san_and_push(move)))
#             elif not san:
#                 san.append((board.fullmove_number) + "..." + (board.san_and_push(move)))
#             else:
#                 san.append(board.san_and_push(move))

#         return " ".join(san)

#     # def parse_san(self, san: str) -> Move:
#     #     if san in ["O-O", "O-O+", "O-O#", "0-0", "0-0+", "0-0#"]:
#     #         return next(
#     #             move
#     #             for move in self.generate_castling_moves()
#     #             if self.is_kingside_castling(move)
#     #         )
#     #     elif san in ["O-O-O", "O-O-O+", "O-O-O#", "0-0-0", "0-0-0+", "0-0-0#"]:
#     #         return next(
#     #             move
#     #             for move in self.generate_castling_moves()
#     #             if self.is_queenside_castling(move)
#     #         )

#     #     to_square = SQUARE_NAMES.index(match.group(4))
#     #     to_mask = BB_SQUARES[to_square] & ~self.occupied_co[self.turn]

#     #     p = match.group(5)
#     #     promotion = PIECE_SYMBOLS.index(p[-1].lower()) if p else None

#     #     from_mask = BB_ALL
#     #     if match.group(2):
#     #         from_file = FILE_NAMES.index(match.group(2))
#     #         from_mask &= BB_FLS[from_file]
#     #     if match.group(3):
#     #         from_rank = int(match.group(3)) - 1
#     #         from_mask &= BB_RKS[from_rank]

#     #     if match.group(1):
#     #         tpe = PIECE_SYMBOLS.index(match.group(1).lower())
#     #         from_mask &= self.pieces_mask(tpe, self.turn)
#     #     elif match.group(2) and match.group(3):

#     #         move = self.find_move(square(from_file, from_rank), to_square, promotion)
#     #         if move.promotion == promotion:
#     #             return move
#     #     else:
#     #         from_mask &= self.pawns

#     #         if not match.group(2):
#     #             from_mask &= BB_FLS[square_file(to_square)]

#     #     matched_move = None
#     #     for move in self.generate_legal_moves(from_mask, to_mask):
#     #         if move.promotion != promotion:
#     #             continue

#     #         matched_move = move
#     #     return matched_move

#     def push_san(self, san: str) -> Move:

#         move = self.parse_san(san)
#         self.push(move)
#         return move

#     def uci(self, move: Move, *, chess960: Optional[bool] = None) -> str:

#         if chess960 is None:
#             chess960 = self.chess960

#         move = self._to_chess960(move)
#         move = self._from_chess960(
#             chess960, move.from_square, move.to_square, move.promotion, move.drop
#         )
#         return move.uci()

#     def parse_uci(self, uci: str) -> Move:

#         move = Move.from_uci(uci)

#         if not move:
#             return move

#         move = self._to_chess960(move)
#         move = self._from_chess960(
#             self.chess960, move.from_square, move.to_square, move.promotion, move.drop
#         )

#         return move

#     def push_uci(self, uci: str) -> Move:

#         move = self.parse_uci(uci)
#         self.push(move)
#         return move

#     def xboard(self, move: Move, chess960: Optional[bool] = None) -> str:
#         if chess960 is None:
#             chess960 = self.chess960

#         if not chess960 or not self.is_castling(move):
#             return move.xboard()
#         elif self.is_kingside_castling(move):
#             return "O-O"
#         else:
#             return "O-O-O"

#     def parse_xboard(self, xboard: str) -> Move:
#         return self.parse_san(xboard)

#     push_xboard = push_san

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

#     def _reduces_castling_rights(self, move: Move) -> bool:
#         cr = self.clean_castling_rights()
#         touched = BB_SQUARES[move.from_square] ^ BB_SQUARES[move.to_square]
#         return bool(
#             touched & cr
#             or cr & BB_RK_1
#             and touched & self.kings & self.occupied_co[WHITE] & ~self.promoted
#             or cr & BB_RK_8
#             and touched & self.kings & self.occupied_co[BLACK] & ~self.promoted
#         )

#     def is_irreversible(self, move: Move) -> bool:

#         return (
#             self.is_zeroing(move)
#             or self._reduces_castling_rights(move)
#             or self.has_legal_en_passant()
#         )

    def is_castling(self, move: Move) -> bool:
        if self.kings & BB_SQUARES[move.from_square]:
            diff = square_file(move.from_square) - square_file(move.to_square)
            return abs(diff) > 1 or bool(
                self.rooks & self.occupied_co[self.turn] & BB_SQUARES[move.to_square]
            )
        return False

#     def is_kingside_castling(self, move: Move) -> bool:

#         return self.is_castling(move) and square_file(move.to_square) > square_file(
#             move.from_square
#         )

#     def is_queenside_castling(self, move: Move) -> bool:

#         return self.is_castling(move) and square_file(move.to_square) < square_file(
#             move.from_square
#         )

    def clean_castling_rights(self) -> Bitboard:
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

#     def has_castling_rights(self, color: Color) -> bool:

#         backrank = BB_RK_1 if color == WHITE else BB_RK_8
#         return bool(self.clean_castling_rights() & backrank)

#     def has_kingside_castling_rights(self, color: Color) -> bool:

#         backrank = BB_RK_1 if color == WHITE else BB_RK_8
#         king_mask = self.kings & self.occupied_co[color] & backrank & ~self.promoted
#         if not king_mask:
#             return False

#         castling_rights = self.clean_castling_rights() & backrank
#         while castling_rights:
#             rook = castling_rights & -castling_rights

#             if rook > king_mask:
#                 return True

#             castling_rights &= castling_rights - 1

#         return False

#     def has_queenside_castling_rights(self, color: Color) -> bool:

#         backrank = BB_RK_1 if color == WHITE else BB_RK_8
#         king_mask = self.kings & self.occupied_co[color] & backrank & ~self.promoted
#         if not king_mask:
#             return False

#         castling_rights = self.clean_castling_rights() & backrank
#         while castling_rights:
#             rook = castling_rights & -castling_rights

#             if rook < king_mask:
#                 return True

#             castling_rights &= castling_rights - 1

#         return False

#     def has_chess960_castling_rights(self) -> bool:

#         chess960 = self.chess960
#         self.chess960 = True
#         castling_rights = self.clean_castling_rights()
#         self.chess960 = chess960

#         if castling_rights & ~BB_COR:
#             return True

#         if (
#             castling_rights & BB_RK_1
#             and not self.occupied_co[WHITE] & self.kings & BB_DICT["BB_E1"]
#         ):
#             return True
#         if (
#             castling_rights & BB_RK_8
#             and not self.occupied_co[BLACK] & self.kings & BB_DICT["BB_E8"]
#         ):
#             return True

#         return False

#     def status(self) -> Status:

#         errors = STATUS_VALID

#         if not self.occupied:
#             errors |= STATUS_EMPTY

#         if not self.occupied_co[WHITE] & self.kings:
#             errors |= STATUS_NO_WHITE_KING
#         if not self.occupied_co[BLACK] & self.kings:
#             errors |= STATUS_NO_BLACK_KING
#         if popcount(self.occupied & self.kings) > 2:
#             errors |= STATUS_TOO_MANY_KINGS

#         if popcount(self.occupied_co[WHITE]) > 16:
#             errors |= STATUS_TOO_MANY_WHITE_PIECES
#         if popcount(self.occupied_co[BLACK]) > 16:
#             errors |= STATUS_TOO_MANY_BLACK_PIECES

#         if popcount(self.occupied_co[WHITE] & self.pawns) > 8:
#             errors |= STATUS_TOO_MANY_WHITE_PAWNS
#         if popcount(self.occupied_co[BLACK] & self.pawns) > 8:
#             errors |= STATUS_TOO_MANY_BLACK_PAWNS

#         if self.pawns & BB_BACKRANKS:
#             errors |= STATUS_PAWNS_ON_BACKRANK

#         if self.castling_rights != self.clean_castling_rights():
#             errors |= STATUS_BAD_CASTLING_RIGHTS

#         valid_ep_square = self._valid_ep_square()
#         if self.ep_square != valid_ep_square:
#             errors |= STATUS_INVALID_EP_SQUARE

#         if self.was_into_check():
#             errors |= STATUS_OPPOSITE_CHECK

#         checkers = self.checkers_mask()
#         our_kings = self.kings & self.occupied_co[self.turn] & ~self.promoted
#         if checkers:
#             if popcount(checkers) > 2:
#                 errors |= STATUS_TOO_MANY_CHECKERS

#             if valid_ep_square is not None:
#                 pushed_to = valid_ep_square ^ SQUARES_DICT["A2"]
#                 pushed_from = valid_ep_square ^ SQUARES_DICT["A4"]
#                 occupied_before = (self.occupied & ~BB_SQUARES[pushed_to]) | BB_SQUARES[
#                     pushed_from
#                 ]
#                 if popcount(checkers) > 1 or (
#                     msb(checkers) != pushed_to
#                     and self._attacked_for_king(our_kings, occupied_before)
#                 ):
#                     errors |= STATUS_IMPOSSIBLE_CHECK
#             else:
#                 if popcount(checkers) > 2 or (
#                     popcount(checkers) == 2
#                     and ray(lsb(checkers), msb(checkers)) & our_kings
#                 ):
#                     errors |= STATUS_IMPOSSIBLE_CHECK

#         return errors

#         if square_rank(self.ep_square) != ep_rank:
#             return None

#         if not self.pawns & self.occupied_co[not self.turn] & pawn_mask:
#             return None

#         if self.occupied & BB_SQUARES[self.ep_square]:
#             return None

#         if self.occupied & seventh_rank_mask:
#             return None

#         return self.ep_square

#     def is_valid(self) -> bool:

#         return self.status() == STATUS_VALID

    def _ep_skewered(self, king: Square, capturer: Square) -> bool:
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

    def _slider_blockers(self, king: Square) -> Bitboard:
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

    def _is_safe(self, king: Square, blockers: Bitboard, move: Move) -> bool:
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
        king: Square,
        checkers: Bitboard,
        from_mask: Bitboard = BB_ALL,
        to_mask: Bitboard = BB_ALL,
    ) -> Iterator[Move]:
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
        self, from_mask: Bitboard = BB_ALL, to_mask: Bitboard = BB_ALL
    ) -> Iterator[Move]:
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

#     def generate_legal_ep(
#         self, from_mask: Bitboard = BB_ALL, to_mask: Bitboard = BB_ALL
#     ) -> Iterator[Move]:
#         if self.is_variant_end():
#             return

#         for move in self.generate_pseudo_legal_ep(from_mask, to_mask):
#             if not self.is_into_check(move):
#                 yield move

#     def generate_legal_captures(
#         self, from_mask: Bitboard = BB_ALL, to_mask: Bitboard = BB_ALL
#     ) -> Iterator[Move]:
#         return itertools.chain(
#             self.generate_legal_moves(
#                 from_mask, to_mask & self.occupied_co[not self.turn]
#             ),
#             self.generate_legal_ep(from_mask, to_mask),
#         )

#     def _attacked_for_king(self, path: Bitboard, occupied: Bitboard) -> bool:
#         return any(
#             self.attackers_mask(not self.turn, sq, occupied)
#             for sq in scan_reversed(path)
#         )

    def generate_castling_moves(
        self, from_mask: Bitboard = BB_ALL, to_mask: Bitboard = BB_ALL
    ) -> Iterator[Move]:
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
        from_square: Square,
        to_square: Square,
        promotion: Optional[PieceType] = None,
        drop: Optional[PieceType] = None,
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

#     def _transposition_key(self) -> Hashable:
#         return (
#             self.pawns,
#             self.knights,
#             self.bishops,
#             self.rooks,
#             self.queens,
#             self.kings,
#             self.occupied_co[WHITE],
#             self.occupied_co[BLACK],
#             self.turn,
#             self.clean_castling_rights(),
#             self.ep_square if self.has_legal_en_passant() else None,
#         )

#     def __repr__(self) -> str:
#         if not self.chess960:
#             return type(self).__name__ + "(" + self.fen() + ")"
#         else:
#             return type(self).__name__ + "(" + self.fen() + ", chess960=True)"

#     def _repr_svg_(self) -> str:
#         import chess.svg

#         return chess.svg.board(
#             board=self,
#             size=390,
#             lastmove=self.peek() if self.move_stack else None,
#             check=self.king(self.turn) if self.is_check() else None,
#         )

#     def __eq__(self, board: object) -> bool:
#         if isinstance(board, Board):
#             return (
#                 self.halfmove_clock == board.halfmove_clock
#                 and self.fullmove_number == board.fullmove_number
#                 and type(self).uci_variant == type(board).uci_variant
#                 and self._transposition_key() == board._transposition_key()
#             )
#         else:
#             return NotImplemented

#     def apply_transform(self, f: Callable[[Bitboard], Bitboard]) -> None:
#         super().apply_transform(f)
#         self.clear_stack()
#         self.ep_square = (
#             None if self.ep_square is None else msb(f(BB_SQUARES[self.ep_square]))
#         )
#         self.castling_rights = f(self.castling_rights)

#     def transform(self, f: Callable[[Bitboard], Bitboard]) -> Self:
#         board = self.copy(stack=False)
#         board.apply_transform(f)
#         return board

#     # def apply_mirror(self) -> None:
#     #     super().apply_mirror()
#     #     self.turn = not self.turn

#     # def mirror(self) -> Self:

#     #     board = self.copy()
#     #     board.apply_mirror()
#     #     return board

#     def copy(self, *, stack: Union[bool, int] = True) -> Self:

#         board = super().copy()

#         board.chess960 = self.chess960

#         board.ep_square = self.ep_square
#         board.castling_rights = self.castling_rights
#         board.turn = self.turn
#         board.fullmove_number = self.fullmove_number
#         board.halfmove_clock = self.halfmove_clock

#         if stack:
#             stack = len(self.move_stack) if stack is True else stack
#             board.move_stack = [copy.copy(move) for move in self.move_stack[-stack:]]
#             board._stack = self._stack[-stack:]

#         return board

#     @classmethod
#     def empty(cls: Type[BoardT], *, chess960: bool = False) -> BoardT:

#         return cls(None, chess960=chess960)

#     @classmethod
#     def from_epd(
#         cls: Type[BoardT], epd: str, *, chess960: bool = False
#     ) -> Tuple[BoardT, Dict[str, Union[None, str, int, float, Move, List[Move]]]]:

#         board = cls.empty(chess960=chess960)
#         return board, board.set_epd(epd)

#     @classmethod
#     def from_chess960_pos(cls: Type[BoardT], scharnagl: int) -> BoardT:
#         board = cls.empty(chess960=True)
#         board.set_chess960_pos(scharnagl)
#         return board


class LegalMoveGenerator:
    def __init__(self, board: Board) -> None:
        self.board = board

    def __iter__(self) -> Iterator[Move]:
        return self.board.generate_legal_moves()


IntoSquareSet: TypeAlias = Union[SupportsInt, Iterable[Square]]


class SquareSet:
    def __init__(self, squares: IntoSquareSet = BB_EMPTY) -> None:
        self.mask: Bitboard = squares.__int__() & BB_ALL
        return

    def __iter__(self) -> Iterator[Square]:
        return scan_forward(self.mask)

    def __len__(self) -> int:
        return popcount(self.mask)

#     def remove(self, square: Square) -> None:
#         mask = BB_SQUARES[square]
#         if self.mask & mask:
#             self.mask ^= mask

    # def pop(self) -> Square:
    #     square = lsb(self.mask)
    #     self.mask &= self.mask - 1
    #     return square

#     def clear(self) -> None:
#         self.mask = BB_EMPTY

    # def carry_rippler(self) -> Iterator[Bitboard]:
    #     return _carry_rippler(self.mask)

#     def tolist(self) -> List[bool]:

#         result = [False] * 64
#         for square in self:
#             result[square] = True
#         return result

#     def __bool__(self) -> bool:
#         return bool(self.mask)

#     def __eq__(self, other: object) -> bool:
#         return self.mask == SquareSet(other).mask

#     def __str__(self) -> str:
#         builder: List[str] = []

#         for square in SQUARES_180:
#             mask = BB_SQUARES[square]
#             builder.append("1" if self.mask & mask else ".")

#             if not mask & BB_FL_H:
#                 builder.append(" ")
#             elif square != SQUARES_DICT["H1"]:
#                 builder.append("\n")

#         return "".join(builder)

#     @classmethod
#     def ray(cls, a: Square, b: Square) -> SquareSet:
#         return cls(ray(a, b))

#     @classmethod
#     def between(cls, a: Square, b: Square) -> SquareSet:
#         return cls(between(a, b))


def calc_heuristic(state: Board):
    if state.is_checkmate():
        return (state.turn * 2 - 1) * -float("inf")

    if (
        state.is_stalemate()
        or state.is_insufficient_material()
        or state.is_fivefold_repetition()
    ):
        return 0

    value = 0

    xFromCen = np.array([1, 2, 3, 4, 5, 3, 2, 1])

    for tpe, val in {
        PAWN: 1,
        KNIGHT: 3,
        BISHOP: 3,
        ROOK: 5,
        QUEEN: 9,
    }.items():
        white_pieces = state.pieces(tpe, WHITE)
        black_pieces = state.pieces(tpe, BLACK)

        value += val * (len(white_pieces) - len(black_pieces))

        if tpe == PAWN:
            for pawn_square in white_pieces:
                rank = square_rank(pawn_square)
                file = square_file(pawn_square)
                value += 0.1 * xFromCen[file] * (rank - 1)

            for pawn_square in black_pieces:
                rank = square_rank(pawn_square)
                file = square_file(pawn_square)
                value -= 0.1 * xFromCen[file] * (6 - rank)

    w_king_square = state.king(WHITE)
    b_king_square = state.king(BLACK)

    if w_king_square is not None:
        w_king_rank = square_rank(w_king_square)
        w_king_file = square_file(w_king_square)
        value += 0.5 * (0.2 * xFromCen[w_king_file] - (w_king_rank))
    if b_king_square is not None:
        b_king_rank = square_rank(b_king_square)
        b_king_file = square_file(b_king_square)
        value += 0.5 * ((0.2 * xFromCen[b_king_file]) + (7 - b_king_rank))

    return value


def minimax(state, depth: int, alpha: float, beta: float, maximizingPlayer):
    global start_time
    if (time.time() - start_time) > time_limit:
        return calc_heuristic(state), None
    if depth == 0:
        return calc_heuristic(state), None

    best_move = None

    moves = list(state.legal_moves)

    def move_value(move):
        return (
            state.is_capture(move)
            + 0.5 * state.gives_check(move)
            + 0.01 * random.random()
        )

    moves.sort(key=move_value, reverse=True)

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

def chess_bot(obs):
    global start_time, time_limit
    
    game = Board(obs.board)
    legal_moves = list(game.legal_moves)
    
    if not legal_moves:
        return "resign"
    
    start_time = time.time()
    time_limit = obs["remainingOverageTime"]/5
    
    _, move = minimax(
        game,
        depth=5,
        alpha=-float("inf"),
        beta=float("inf"),
        maximizingPlayer=game.turn,
    )
    
    if move is None:
        move = random.choice(legal_moves)

    return str(move)
