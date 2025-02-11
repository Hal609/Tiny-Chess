#include <Python.h>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>
#include <array>
#include <algorithm>
#include <stdexcept>
#include <cmath>
#include <bitset>
#include <cstdint>
#include <map>
#include <iterator>
#include <optional>

// -----------------------------------------------------------------------------
// Basic Type Aliases & Constants
// -----------------------------------------------------------------------------
using std::size_t;

using Bitboard = uint64_t; // 64-bit integer for bitboards
using Square = int;        // 0..63
using Color = bool;        // true = White, false = Black (or vice versa)

// For clarity (the Python code uses True=White, False=Black).
static const bool WHITE = true;
static const bool BLACK = false;

// PieceTypes
// 1=pawn, 2=knight, 3=bishop, 4=rook, 5=queen, 6=king
using PieceType = int;
static const int PAWN = 1;
static const int KNIGHT = 2;
static const int BISHOP = 3;
static const int ROOK = 4;
static const int QUEEN = 5;
static const int KING = 6;

// For mapping piece symbols, e.g. 1->"p", 2->"n", etc.
static std::vector<std::string> PIECE_SYMBOLS = {"", "p", "n", "b", "r", "q", "k"};

// Files "a" through "h"
static std::vector<std::string> FILE_NAMES{"a", "b", "c", "d", "e", "f", "g", "h"};

// Ranks "1" through "8"
static std::vector<std::string> RANK_NAMES{"1", "2", "3", "4", "5", "6", "7", "8"};

std::string piece_symbol(PieceType piece_type)
{
    return (std::string)PIECE_SYMBOLS[piece_type];
}

// // The standard starting FEN
// static const std::string STARTING_FEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";

// // -----------------------------------------------------------------------------
// // Squares and Bitboard constants
// // -----------------------------------------------------------------------------

// Square definitions 0..63, in Python code (A1=0, B1=1, ..., H8=63).
// We'll just define them manually:
static const Square A1 = 0, B1 = 1, C1 = 2, D1 = 3, E1 = 4, F1 = 5, G1 = 6, H1 = 7;
static const Square A2 = 8, B2 = 9, C2 = 10, D2 = 11, E2 = 12, F2 = 13, G2 = 14, H2 = 15;
static const Square A3 = 16, B3 = 17, C3 = 18, D3 = 19, E3 = 20, F3 = 21, G3 = 22, H3 = 23;
static const Square A4 = 24, B4 = 25, C4 = 26, D4 = 27, E4 = 28, F4 = 29, G4 = 30, H4 = 31;
static const Square A5 = 32, B5 = 33, C5 = 34, D5 = 35, E5 = 36, F5 = 37, G5 = 38, H5 = 39;
static const Square A6 = 40, B6 = 41, C6 = 42, D6 = 43, E6 = 44, F6 = 45, G6 = 46, H6 = 47;
static const Square A7 = 48, B7 = 49, C7 = 50, D7 = 51, E7 = 52, F7 = 53, G7 = 54, H7 = 55;
static const Square A8 = 56, B8 = 57, C8 = 58, D8 = 59, E8 = 60, F8 = 61, G8 = 62, H8 = 63;

// // We'll create a global array SQUARES = [0..63].
static std::vector<Square> SQUARES{
    0, 1, 2, 3, 4, 5, 6, 7,
    8, 9, 10, 11, 12, 13, 14, 15,
    16, 17, 18, 19, 20, 21, 22, 23,
    24, 25, 26, 27, 28, 29, 30, 31,
    32, 33, 34, 35, 36, 37, 38, 39,
    40, 41, 42, 43, 44, 45, 46, 47,
    48, 49, 50, 51, 52, 53, 54, 55,
    56, 57, 58, 59, 60, 61, 62, 63};

const std::vector<std::string> SQUARE_NAMES = {
    "a1", "b1", "c1", "d1", "e1", "f1", "g1", "h1",
    "a2", "b2", "c2", "d2", "e2", "f2", "g2", "h2",
    "a3", "b3", "c3", "d3", "e3", "f3", "g3", "h3",
    "a4", "b4", "c4", "d4", "e4", "f4", "g4", "h4",
    "a5", "b5", "c5", "d5", "e5", "f5", "g5", "h5",
    "a6", "b6", "c6", "d6", "e6", "f6", "g6", "h6",
    "a7", "b7", "c7", "d7", "e7", "f7", "g7", "h7",
    "a8", "b8", "c8", "d8", "e8", "f8", "g8", "h8"};

// Square parse_square(const std::string &name)
// {
//     auto it = std::find(SQUARE_NAMES.begin(), SQUARE_NAMES.end(), name);
//     if (it == SQUARE_NAMES.end())
//     {
//         throw std::invalid_argument("Invalid square name");
//     }
//     return std::distance(SQUARE_NAMES.begin(), it);
// }

// std::string square_name(Square square)
// {
//     return SQUARE_NAMES[square];
// }

// Square square(int file_index, int rank_index)
// {
//     return rank_index * 8 + file_index;
// }

// A small helper to get the file of a square (0..7).
static int square_file(Square sq)
{
    return sq & 7;
}

// A small helper to get the rank of a square (0..7).
static int square_rank(Square sq)
{
    return sq >> 3;
}

static int square_distance(Square a, Square b)
{
    return std::max(abs(square_file(a) - square_file(b)), abs(square_rank(a) - square_rank(b)));
}

// // Return the SQUARE_NAMES[sq].
// static std::string get_square_name(Square sq)
// {
//     // We built SQUARE_NAMES in rank/file order, but note:
//     // SQUARE_NAMES[0] = "a1", SQUARE_NAMES[1] = "b1", ...
//     // That matches your approach if we do it consistently
//     if (sq < 0 || sq >= 64)
//         return "??";
//     return SQUARE_NAMES[sq];
// }

Square square_mirror(Square square)
{
    return square ^ 0x38;
}

static std::array<Bitboard, 64> SQUARES_180 = []
{
    std::array<Bitboard, 64> arr = {};
    for (int sq = 0; sq < 64; ++sq)
    {
        arr[sq] = square_mirror(sq);
    }
    return arr;
}();

// // A couple of simple bitboard constants:
static const Bitboard BB_EMPTY = 0x0000000000000000;
static const Bitboard BB_ALL = 0xffffffffffffffffULL;

// Single-square bitboards
static const Bitboard BB_A1 = (1ULL << A1);
// static const Bitboard BB_B1 = (1ULL << B1);
// static const Bitboard BB_C1 = (1ULL << C1);
// static const Bitboard BB_D1 = (1ULL << D1);
static const Bitboard BB_E1 = (1ULL << E1);
// static const Bitboard BB_F1 = (1ULL << F1);
// static const Bitboard BB_G1 = (1ULL << G1);
static const Bitboard BB_H1 = (1ULL << H1);
// static const Bitboard BB_A2 = (1ULL << A2);
// static const Bitboard BB_B2 = (1ULL << B2);
// static const Bitboard BB_C2 = (1ULL << C2);
// static const Bitboard BB_D2 = (1ULL << D2);
// static const Bitboard BB_E2 = (1ULL << E2);
// static const Bitboard BB_F2 = (1ULL << F2);
// static const Bitboard BB_G2 = (1ULL << G2);
// static const Bitboard BB_H2 = (1ULL << H2);
// static const Bitboard BB_A3 = (1ULL << A3);
// static const Bitboard BB_B3 = (1ULL << B3);
// static const Bitboard BB_C3 = (1ULL << C3);
// static const Bitboard BB_D3 = (1ULL << D3);
// static const Bitboard BB_E3 = (1ULL << E3);
// static const Bitboard BB_F3 = (1ULL << F3);
// static const Bitboard BB_G3 = (1ULL << G3);
// static const Bitboard BB_H3 = (1ULL << H3);
// static const Bitboard BB_A4 = (1ULL << A4);
// static const Bitboard BB_B4 = (1ULL << B4);
// static const Bitboard BB_C4 = (1ULL << C4);
// static const Bitboard BB_D4 = (1ULL << D4);
// static const Bitboard BB_E4 = (1ULL << E4);
// static const Bitboard BB_F4 = (1ULL << F4);
// static const Bitboard BB_G4 = (1ULL << G4);
// static const Bitboard BB_H4 = (1ULL << H4);
// static const Bitboard BB_A5 = (1ULL << A5);
// static const Bitboard BB_B5 = (1ULL << B5);
// static const Bitboard BB_C5 = (1ULL << C5);
// static const Bitboard BB_D5 = (1ULL << D5);
// static const Bitboard BB_E5 = (1ULL << E5);
// static const Bitboard BB_F5 = (1ULL << F5);
// static const Bitboard BB_G5 = (1ULL << G5);
// static const Bitboard BB_H5 = (1ULL << H5);
// static const Bitboard BB_A6 = (1ULL << A6);
// static const Bitboard BB_B6 = (1ULL << B6);
// static const Bitboard BB_C6 = (1ULL << C6);
// static const Bitboard BB_D6 = (1ULL << D6);
// static const Bitboard BB_E6 = (1ULL << E6);
// static const Bitboard BB_F6 = (1ULL << F6);
// static const Bitboard BB_G6 = (1ULL << G6);
// static const Bitboard BB_H6 = (1ULL << H6);
// static const Bitboard BB_A7 = (1ULL << A7);
// static const Bitboard BB_B7 = (1ULL << B7);
// static const Bitboard BB_C7 = (1ULL << C7);
// static const Bitboard BB_D7 = (1ULL << D7);
// static const Bitboard BB_E7 = (1ULL << E7);
// static const Bitboard BB_F7 = (1ULL << F7);
// static const Bitboard BB_G7 = (1ULL << G7);
// static const Bitboard BB_H7 = (1ULL << H7);
static const Bitboard BB_A8 = (1ULL << A8);
// static const Bitboard BB_B8 = (1ULL << B8);
static const Bitboard BB_C8 = (1ULL << C8);
static const Bitboard BB_D8 = (1ULL << D8);
static const Bitboard BB_E8 = (1ULL << E8);
// static const Bitboard BB_F8 = (1ULL << F8);
// static const Bitboard BB_G8 = (1ULL << G8);
static const Bitboard BB_H8 = (1ULL << H8);

static std::array<Bitboard, 64> BB_SQUARES = []
{
    std::array<Bitboard, 64> arr = {};
    for (int sq = 0; sq < 64; ++sq)
    {
        arr[sq] = (1ULL << sq);
    }
    return arr;
}();

// static const Bitboard BB_CORNERS = BB_A1 | BB_H1 | BB_A8 | BB_H8;
// static const Bitboard BB_CENTER = BB_D4 | BB_E4 | BB_D5 | BB_E5;

// static const Bitboard BB_LIGHT_SQUARES = 0x55aa55aa55aa55aaULL;
// static const Bitboard BB_DARK_SQUARES = 0xaa55aa55aa55aa55ULL;

// Files
static const Bitboard BB_FILE_A = (0x0101010101010101ULL << 0);
static const Bitboard BB_FILE_B = (0x0101010101010101ULL << 1);
static const Bitboard BB_FILE_C = (0x0101010101010101ULL << 2);
static const Bitboard BB_FILE_D = (0x0101010101010101ULL << 3);
static const Bitboard BB_FILE_E = (0x0101010101010101ULL << 4);
static const Bitboard BB_FILE_F = (0x0101010101010101ULL << 5);
static const Bitboard BB_FILE_G = (0x0101010101010101ULL << 6);
static const Bitboard BB_FILE_H = (0x0101010101010101ULL << 7);

static const std::array<Bitboard, 8> BB_FILES = {
    BB_FILE_A, BB_FILE_B, BB_FILE_C, BB_FILE_D,
    BB_FILE_E, BB_FILE_F, BB_FILE_G, BB_FILE_H};

// Ranks
static const Bitboard BB_RANK_1 = (0xffULL << (8 * 0));
static const Bitboard BB_RANK_2 = (0xffULL << (8 * 1));
static const Bitboard BB_RANK_3 = (0xffULL << (8 * 2));
static const Bitboard BB_RANK_4 = (0xffULL << (8 * 3));
static const Bitboard BB_RANK_5 = (0xffULL << (8 * 4));
static const Bitboard BB_RANK_6 = (0xffULL << (8 * 5));
static const Bitboard BB_RANK_7 = (0xffULL << (8 * 6));
static const Bitboard BB_RANK_8 = (0xffULL << (8 * 7));

static const std::array<Bitboard, 8> BB_RANKS = {
    BB_RANK_1, BB_RANK_2, BB_RANK_3, BB_RANK_4,
    BB_RANK_5, BB_RANK_6, BB_RANK_7, BB_RANK_8};

// static const Bitboard BB_BACKRANKS = (BB_RANK_1 | BB_RANK_8);

Bitboard _sliding_attacks(Square square, Bitboard occupied, const std::vector<int> &deltas)
{
    Bitboard attacks = BB_EMPTY;
    for (auto delta : deltas)
    {
        Square sq = square;

        while (true)
        {
            sq += delta;
            if (!(0 <= sq && sq < 64) || square_distance(sq, sq - delta) > 2)
            {
                break;
            }
            attacks |= BB_SQUARES[sq];

            if (occupied & BB_SQUARES[sq])
            {
                break;
            }
        }
    }

    return attacks;
}

Bitboard _step_attacks(Square square, std::vector<int> deltas)
{
    return _sliding_attacks(square, BB_ALL, deltas);
}

std::vector<Bitboard> BB_KNIGHT_ATTACKS;
std::vector<Bitboard> BB_KING_ATTACKS;
std::vector<std::vector<Bitboard>> BB_PAWN_ATTACKS;

Bitboard _edges(Square square)
{
    return (((BB_RANK_1 | BB_RANK_8) & ~BB_RANKS[square_rank(square)]) |
            ((BB_FILE_A | BB_FILE_H) & ~BB_FILES[square_file(square)]));
}

std::vector<Bitboard> _carry_rippler(Bitboard mask)
{
    std::vector<Bitboard> subsets;
    Bitboard subset = BB_EMPTY;
    while (true)
    {
        subsets.push_back(subset);
        subset = (subset - mask) & mask;
        if (!subset)
        {
            break;
        }
    }
    return subsets;
}

std::pair<std::vector<Bitboard>, std::vector<std::unordered_map<Bitboard, Bitboard>>> _attack_table(const std::vector<int> &deltas)
{
    std::vector<Bitboard> mask_table;
    std::vector<std::unordered_map<Bitboard, Bitboard>> attack_table;

    for (Square square : SQUARES)
    {
        std::unordered_map<Bitboard, Bitboard> attacks;

        Bitboard mask = _sliding_attacks(square, 0, deltas) & ~_edges(square);
        std::vector<Bitboard> subsets = _carry_rippler(mask);
        for (Bitboard subset : subsets)
        {
            attacks[subset] = _sliding_attacks(square, subset, deltas);
        }

        attack_table.push_back(attacks);
        mask_table.push_back(mask);
    }

    return {mask_table, attack_table};
}

void initialize_attack_tables()
{
    std::vector<int> knight_deltas = {17, 15, 10, 6, -17, -15, -10, -6};
    std::vector<int> king_deltas = {9, 8, 7, 1, -9, -8, -7, -1};
    std::vector<std::vector<int>> pawn_deltas = {{-7, -9}, {7, 9}};

    for (Square sq : SQUARES)
    {
        BB_KNIGHT_ATTACKS.push_back(_step_attacks(sq, knight_deltas));
        BB_KING_ATTACKS.push_back(_step_attacks(sq, king_deltas));
    }

    for (const auto &deltas : pawn_deltas)
    {
        std::vector<Bitboard> pawn_attacks;
        for (Square sq : SQUARES)
        {
            pawn_attacks.push_back(_step_attacks(sq, deltas));
        }
        BB_PAWN_ATTACKS.push_back(pawn_attacks);
    }
}

auto [BB_DIAG_MASKS, BB_DIAG_ATTACKS] = _attack_table({-9, -7, 7, 9});
auto [BB_FILE_MASKS, BB_FILE_ATTACKS] = _attack_table({-8, 8});
auto [BB_RANK_MASKS, BB_RANK_ATTACKS] = _attack_table({-1, 1});

std::vector<std::vector<Bitboard>> _rays()
{
    std::vector<std::vector<Bitboard>> rays;
    for (size_t a = 0; a < BB_SQUARES.size(); a++)
    {
        Bitboard bb_a = BB_SQUARES[a];
        std::vector<Bitboard> rays_row;

        for (size_t b = 0; b < BB_SQUARES.size(); b++)
        {
            Bitboard bb_b = BB_SQUARES[b];
            if (BB_DIAG_ATTACKS[a][0] & bb_b)
            {
                rays_row.push_back((BB_DIAG_ATTACKS[a][0] & BB_DIAG_ATTACKS[b][0]) | bb_a | bb_b);
            }
            else if (BB_RANK_ATTACKS[a][0] & bb_b)
            {
                rays_row.push_back(BB_RANK_ATTACKS[a][0] | bb_a);
            }
            else if (BB_FILE_ATTACKS[a][0] & bb_b)
            {
                rays_row.push_back(BB_FILE_ATTACKS[a][0] | bb_a);
            }
            else
            {
                rays_row.push_back(BB_EMPTY);
            }
        }
        rays.push_back(rays_row);
    }
    return rays;
}

std::vector<std::vector<Bitboard>> BB_RAYS;

// // -----------------------------------------------------------------------------
// // Some Helper Functions
// // -----------------------------------------------------------------------------

// bit_length of a 64-bit integer (like Python's .bit_length())
static int bit_length(uint64_t x)
{
    // number of bits needed to represent x
    // a fallback approach: 64 - __builtin_clzll(x)
    if (x == 0ULL)
        return 0;
    return 64 - __builtin_clzll(x);
}

// Return index of LSB (like Python's (bb & -bb).bit_length()-1).
static int lsb(Bitboard bb)
{
    if (bb == 0ULL)
    {
        return -1; // no bits set
    }
    // isolate the lowest set bit
    Bitboard isolated = (bb & -(int64_t)bb);
    return bit_length(isolated) - 1;
}

// Return index of MSB
static int msb(Bitboard bb)
{
    if (bb == 0ULL)
    {
        return -1; // no bits set
    }
    return bit_length(bb) - 1;
}

// // Count set bits. (Equivalent to Python's popcount.)
// static int popcount(Bitboard bb)
// {
//     return __builtin_popcountll((unsigned long long)bb);
// }

// // For iteration over set bits from LSB to MSB:
// static std::vector<int> scan_forward(Bitboard bb)
// {
//     std::vector<int> result;
//     while (bb)
//     {
//         int i = lsb(bb);
//         result.push_back(i);
//         bb ^= (1ULL << i);
//     }
//     return result;
// }

// For iteration over set bits from MSB to LSB:
static std::vector<int> scan_reversed(Bitboard bb)
{
    std::vector<int> result;
    while (bb)
    {
        int r = bit_length(bb) - 1;
        result.push_back(r);
        bb ^= BB_SQUARES[r];
    }
    return result;
}

Bitboard ray(Square a, Square b)
{
    return BB_RAYS[a][b];
}

Bitboard between(Square a, Square b)
{
    Bitboard bb = BB_RAYS[a][b] & ((BB_ALL << a) ^ (BB_ALL << b));
    return bb & (bb - 1);
}

class Board; // Forward declaration

// -----------------------------------------------------------------------------
// Piece Class
// -----------------------------------------------------------------------------
class Piece
{
public:
    PieceType piece_type;
    Color color;

    Piece(PieceType type, Color col) : piece_type(type), color(col) {}
    static Piece from_symbol(char symbol_char);

    std::string symbol() const
    {
        std::string symbol = piece_symbol(piece_type);
        if (color == WHITE)
        {
            std::transform(symbol.begin(), symbol.end(), symbol.begin(), ::toupper);
        }
        return symbol;
    }

    //     friend std::ostream &operator<<(std::ostream &os, const Piece &p)
    //     {
    //         os << "Piece(" << p.symbol() << ")";
    //         return os;
    //     }
};

Piece Piece::from_symbol(char symbol_char)
{
    bool isWhite = std::isupper(static_cast<unsigned char>(symbol_char)) != 0;
    char lower = static_cast<char>(std::tolower(static_cast<unsigned char>(symbol_char)));

    // find index in PIECE_SYMBOLS
    // e.g. 1->"p",2->"n",3->"b",4->"r",5->"q",6->"k"
    auto it = std::find(PIECE_SYMBOLS.begin(), PIECE_SYMBOLS.end(), std::string(1, lower));
    int index = static_cast<int>(it - PIECE_SYMBOLS.begin());

    return Piece(static_cast<PieceType>(index), isWhite);
}

// -----------------------------------------------------------------------------
// _BoardState Class
// -----------------------------------------------------------------------------
class _BoardState
{
public:
    Bitboard pawns;
    Bitboard knights;
    Bitboard bishops;
    Bitboard rooks;
    Bitboard queens;
    Bitboard kings;

    Bitboard occupied_w;
    Bitboard occupied_b;
    Bitboard occupied;

    Bitboard promoted;

    bool turn;
    Bitboard castling_rights;
    int ep_square;
    int halfmove_clock;
    int fullmove_number;

    _BoardState(Board board);
    void restore(Board board);
};

// // -----------------------------------------------------------------------------
// // Move Class
// // -----------------------------------------------------------------------------
class Move
{
public:
    Square from_square;
    Square to_square;
    //     // Optional promotion piece (1..6) or 0 if no promotion
    int promotion;
    //     // Optional drop piece (1..6) or 0 if no drop
    int drop;

    Move(Square fromS, Square toS, int promo = 0, int d = 0)
        : from_square(fromS), to_square(toS), promotion(promo), drop(d)
    {
    }

    // Move() : from_square(0), to_square(0), promotion(0), drop(0) {}

    // Returns a UCI string
    std::string uci() const
    {
        if (drop)
        {
            std::string upper_symb = std::string(1, toupper(piece_symbol(drop)[0]));
            return upper_symb + "@" + SQUARE_NAMES[to_square];
        }
        else if (promotion)
        {
            return SQUARE_NAMES[from_square] + SQUARE_NAMES[to_square] + piece_symbol(promotion);
        }
        else
        {
            return SQUARE_NAMES[from_square] + SQUARE_NAMES[to_square];
        }
    }

    //     // Evaluate to `false` if null move
    //     explicit operator bool() const
    //     {
    //         // In Python: return bool(from_square or to_square or promotion or drop)
    //         return (from_square != 0 || to_square != 0 || promotion != 0 || drop != 0);
    //     }

    //     // Static helper: Null move
    //     static Move null_move()
    //     {
    //         return Move(0, 0, 0, 0);
    //     }

    //     // For debugging
    //     std::string str() const
    //     {
    //         return uci();
    //     }
};

// // -----------------------------------------------------------------------------
// // Simple "LegalMoveGenerator"-like Class
// // In Python it's an iterator/generator. We'll store the moves in a vector.
// // -----------------------------------------------------------------------------

// class LegalMoveGenerator
// {
// public:
//     Board *board;
//     // We'll store all moves once, or generate on the fly.

//     // constructor
//     LegalMoveGenerator(Board *b) : board(b) {}

//     std::vector<Move> all_legal_moves();
//     int count();
//     bool contains(const Move &move);
// };

// -----------------------------------------------------------------------------
// Board Class (partial translation)
// -----------------------------------------------------------------------------
class Board
{
public:
    // We'll store piece bitboards
    Bitboard pawns;
    Bitboard knights;
    Bitboard bishops;
    Bitboard rooks;
    Bitboard queens;
    Bitboard kings;

    // Occupancy by color
    Bitboard occupied_co[2];
    Bitboard occupied;
    Bitboard promoted; // bitboard of promoted pieces

    bool turn; // white=TRUE or black=FALSE
    Bitboard castling_rights;
    int halfmove_clock;
    int fullmove_number;
    // For brevity, we skip some state or store them here
    int ep_square; // -1 if none

    // // We'll store the moves made
    std::vector<Move> move_stack;

    // // std::optional<Square> ep_square;
    std::vector<_BoardState> _stack;

    Board(std::optional<std::string> fen)
    {
        occupied_co[WHITE] = BB_EMPTY;
        occupied_co[BLACK] = BB_EMPTY;

        _clear_board();

        set_fen(fen.value());
    }

    std::optional<PieceType> piece_type_at(Square square)
    {
        Bitboard mask = BB_SQUARES[square];

        if (!(occupied & mask))
        {
            return 0ULL;
        }
        else if (pawns & mask)
        {
            return PAWN;
        }
        else if (knights & mask)
        {
            return KNIGHT;
        }
        else if (bishops & mask)
        {
            return BISHOP;
        }
        else if (rooks & mask)
        {
            return ROOK;
        }
        else if (queens & mask)
        {
            return QUEEN;
        }
        else
        {
            return KING;
        }
    }

    std::optional<PieceType> _remove_piece_at(Square square)
    {
        std::optional<PieceType> piece_type = piece_type_at(square);
        Bitboard mask = BB_SQUARES[square];

        if (piece_type == PAWN)
        {
            pawns ^= mask;
        }
        else if (piece_type == KNIGHT)
        {
            knights ^= mask;
        }
        else if (piece_type == BISHOP)
        {
            bishops ^= mask;
        }
        else if (piece_type == ROOK)
        {
            rooks ^= mask;
        }
        else if (piece_type == QUEEN)
        {
            queens ^= mask;
        }
        else if (piece_type == KING)
        {
            kings ^= mask;
        }
        else
        {
            return 0ULL;
        }

        occupied ^= mask;
        occupied_co[WHITE] &= ~mask;
        occupied_co[BLACK] &= ~mask;

        promoted &= ~mask;

        return piece_type;
    }

    void _set_piece_at(Square square, PieceType piece_type, Color color, std::optional<bool> promoted = false)
    {
        _remove_piece_at(square);

        Bitboard mask = BB_SQUARES[square];

        if (piece_type == PAWN)
        {
            pawns |= mask;
        }
        else if (piece_type == KNIGHT)
        {
            knights |= mask;
        }
        else if (piece_type == BISHOP)
        {
            bishops |= mask;
        }
        else if (piece_type == ROOK)
        {
            rooks |= mask;
        }
        else if (piece_type == QUEEN)
        {
            queens |= mask;
        }
        else if (piece_type == KING)
        {
            kings |= mask;
        }

        occupied ^= mask;
        occupied_co[color] ^= mask;

        if (promoted)
        {
            promoted = promoted.value() ^ mask;
        }
    }

    void _set_board_fen(std::string fen)
    {
        // Clear the board.
        _clear_board();

        // Put pieces on the board.
        int square_index = 0;
        for (char c : fen)
        {
            std::string c_lower(1, (char)tolower(c));
            int c_lower_symbol_index = count(PIECE_SYMBOLS.begin(), PIECE_SYMBOLS.end(), c_lower);
            if (c >= '1' && c <= '8')
            {
                int steps = c - '0'; // '3' => 3
                square_index += steps;
            }
            else if (c_lower_symbol_index > 0)
            {
                Piece piece = Piece::from_symbol(c);
                _set_piece_at(SQUARES_180[square_index], piece.piece_type, piece.color);
                square_index += 1;
            }
            else if (c == '~')
            {
                promoted |= BB_SQUARES[SQUARES_180[square_index - 1]];
            }
        }
    }

    void _set_castling_fen(std::string castling_fen)
    {
        if (castling_fen == "-")
        {
            castling_rights = BB_EMPTY;
            return;
        }
        castling_rights = BB_EMPTY;

        for (char flag : castling_fen)
        {
            Color color = std::isupper(flag) ? WHITE : BLACK;
            flag = (char)tolower(flag);
            Bitboard backrank = (color == WHITE) ? BB_RANK_1 : BB_RANK_8;
            Bitboard local_rooks = occupied_co[color] & rooks & backrank;
            std::optional<PieceType> local_king = king(color);

            if (flag == 'q')
            {
                if ((local_king != 0ULL) && (lsb(rooks) < local_king))
                {
                    castling_rights |= rooks & -rooks;
                }
                else
                {
                    castling_rights |= BB_FILE_A & backrank;
                }
            }
            else if (flag == 'k')
            {
                Bitboard rook = msb(local_rooks);
                if ((local_king != 0ULL) && (local_king < rook))
                {
                    castling_rights |= BB_SQUARES[rook];
                }
                else
                {
                    castling_rights |= BB_FILE_H & backrank;
                }
            }
            else
            {
                std::string flag_string(1, flag);
                int filename_index = std::find(FILE_NAMES.begin(), FILE_NAMES.end(), flag_string) != FILE_NAMES.end();
                castling_rights |= BB_FILES[filename_index] & backrank;
            }
        }
    }

    void set_fen(std::string fen)
    {
        std::istringstream iss(fen);
        std::vector<std::string> parts;
        {
            std::string token;
            while (iss >> token)
            {
                parts.push_back(token);
            }
        }

        // Board part.
        std::string board_part = parts[0];
        parts.erase(parts.begin());
        std::string turn_part = parts[0];
        parts.erase(parts.begin());

        turn = (turn_part == "w") ? WHITE : BLACK;

        std::string castling_part = parts[0];
        parts.erase(parts.begin());
        std::string ep_part = parts[0];
        parts.erase(parts.begin());
        std::string halfmove_part = parts[0];
        parts.erase(parts.begin());
        std::string fullmove_part = parts[0];
        parts.erase(parts.begin());

        // Validate the board part and set it.
        _set_board_fen(board_part);

        // Apply.
        _set_castling_fen(castling_part);
        int squarename_index = std::find(SQUARE_NAMES.begin(), SQUARE_NAMES.end(), ep_part) != SQUARE_NAMES.end();
        ep_square = (ep_part == "-") ? 0ULL : squarename_index;
        halfmove_clock = std::stoi(fullmove_part);
        fullmove_number = std::stoi(fullmove_part);
        clear_stack();
    }

    void clear_stack()
    {
        move_stack.clear();
        _stack.clear();
    }

    void _clear_board()
    {
        pawns = BB_EMPTY;
        knights = BB_EMPTY;
        bishops = BB_EMPTY;
        rooks = BB_EMPTY;
        queens = BB_EMPTY;
        kings = BB_EMPTY;

        promoted = BB_EMPTY;

        occupied_co[WHITE] = BB_EMPTY;
        occupied_co[BLACK] = BB_EMPTY;
        occupied = BB_EMPTY;
    }

    //     // A simple reset to a standard start
    //     void reset()
    //     {
    //         // Clear
    //         pawns = 0ULL;
    //         knights = 0ULL;
    //         bishops = 0ULL;
    //         rooks = 0ULL;
    //         queens = 0ULL;
    //         kings = 0ULL;
    //         promoted = 0ULL;

    //         occupied_co[WHITE] = 0ULL;
    //         occupied_co[BLACK] = 0ULL;
    //         occupied = 0ULL;

    //         turn = WHITE;
    //         castling_rights = BB_CORNERS; // corners => A1,H1,A8,H8
    //         halfmove_clock = 0;
    //         fullmove_number = 1;
    //         ep_square = -1; // None

    //         // Setup standard chess arrangement
    //         // White pawns => rank2
    //         for (int sq = A2; sq <= H2; ++sq)
    //         {
    //             pawns |= (1ULL << sq);
    //             occupied_co[WHITE] |= (1ULL << sq);
    //         }
    //         // Black pawns => rank7
    //         for (int sq = A7; sq <= H7; ++sq)
    //         {
    //             pawns |= (1ULL << sq);
    //             occupied_co[BLACK] |= (1ULL << sq);
    //         }
    //         // White knights => B1,G1
    //         knights |= (1ULL << B1);
    //         knights |= (1ULL << G1);
    //         occupied_co[WHITE] |= (1ULL << B1);
    //         occupied_co[WHITE] |= (1ULL << G1);

    //         // Black knights => B8,G8
    //         knights |= (1ULL << B8);
    //         knights |= (1ULL << G8);
    //         occupied_co[BLACK] |= (1ULL << B8);
    //         occupied_co[BLACK] |= (1ULL << G8);

    //         // White bishops => C1,F1
    //         bishops |= (1ULL << C1);
    //         bishops |= (1ULL << F1);
    //         occupied_co[WHITE] |= (1ULL << C1);
    //         occupied_co[WHITE] |= (1ULL << F1);

    //         // Black bishops => C8,F8
    //         bishops |= (1ULL << C8);
    //         bishops |= (1ULL << F8);
    //         occupied_co[BLACK] |= (1ULL << C8);
    //         occupied_co[BLACK] |= (1ULL << F8);

    //         // White rooks => A1,H1
    //         rooks |= (1ULL << A1);
    //         rooks |= (1ULL << H1);
    //         occupied_co[WHITE] |= (1ULL << A1);
    //         occupied_co[WHITE] |= (1ULL << H1);

    //         // Black rooks => A8,H8
    //         rooks |= (1ULL << A8);
    //         rooks |= (1ULL << H8);
    //         occupied_co[BLACK] |= (1ULL << A8);
    //         occupied_co[BLACK] |= (1ULL << H8);

    //         // White queen => D1
    //         queens |= (1ULL << D1);
    //         occupied_co[WHITE] |= (1ULL << D1);

    //         // Black queen => D8
    //         queens |= (1ULL << D8);
    //         occupied_co[BLACK] |= (1ULL << D8);

    //         // White king => E1
    //         kings |= (1ULL << E1);
    //         occupied_co[WHITE] |= (1ULL << E1);

    //         // Black king => E8
    //         kings |= (1ULL << E8);
    //         occupied_co[BLACK] |= (1ULL << E8);

    //         // Occupied is union
    //         occupied = occupied_co[WHITE] | occupied_co[BLACK];
    //         move_stack.clear();
    //     }

    std::optional<Square> king(Color color) const
    {
        Bitboard king_mask = (occupied_co[color] & kings & ~promoted);
        if (king_mask == 0ULL)
        {
            // No king => std::nullopt
            return std::nullopt;
        }
        else
        {
            // Single (or multiple) bits => return the MSB
            return msb(king_mask);
        }
    }

    //     // Minimal function: is the game "ended" for a normal variant?
    //     bool is_variant_end()
    //     {
    //         // In python code: not all has_pieces for has_pieces in occupied_co
    //         // We'll just check if either side has no pieces
    //         bool white_has = (occupied_co[WHITE] != 0ULL);
    //         bool black_has = (occupied_co[BLACK] != 0ULL);
    //         return !(white_has && black_has);
    //     }

    Bitboard _slider_blockers(Square king)
    {
        Bitboard rooks_and_queens = rooks | queens;
        Bitboard bishops_and_queens = bishops | queens;

        Bitboard snipers = ((BB_RANK_ATTACKS[king][0] & rooks_and_queens) |
                            (BB_FILE_ATTACKS[king][0] & rooks_and_queens) |
                            (BB_DIAG_ATTACKS[king][0] & bishops_and_queens));

        Bitboard blockers = 0;

        for (Square sniper : scan_reversed(snipers & occupied_co[!turn]))
        {
            Bitboard b = between(king, sniper) & occupied;

            // Add to blockers if exactly one piece in-between.
            if (b && BB_SQUARES[msb(b)] == b)
            {
                blockers |= b;
            }
        }

        return blockers & occupied_co[turn];
    }

    std::vector<Move> _generate_evasions(Square king, Bitboard checkers, Bitboard from_mask /*= BB_ALL*/, Bitboard to_mask /*= BB_ALL*/)
    {
        Bitboard sliders = checkers & (bishops | rooks | queens);

        std::vector<Move> moves;

        Bitboard attacked = 0ULL;
        {
            // For each slider in descending order
            for (int checker : scan_reversed(sliders))
            {
                attacked |= ray(king, checker) & ~BB_SQUARES[checker];
            }
        }

        if ((BB_SQUARES[king] & from_mask) != 0ULL)
        {
            Bitboard king_moves = BB_KING_ATTACKS[king] & ~occupied_co[turn] // cannot land on own pieces
                                  & ~attacked                                // cannot land on squares attacked by the slider
                                  & to_mask;                                 // must also satisfy the caller's to_mask

            // For each possible king target
            for (int to_square : scan_reversed(king_moves))
            {
                moves.emplace_back(Move(king, to_square));
            }
        }

        // 4) If exactly one checker, we can try blocking or capturing it.
        int checker_sq = msb(checkers); // get index of the most significant bit

        // If checkers has only this single bit set => single checker
        if (BB_SQUARES[checker_sq] == checkers)
        {
            // 4a) The block-or-capture squares = the line between king and checker + the checker itself
            Bitboard target = between(king, checker_sq) | checkers;

            // 4b) Generate all pseudo-legal moves that move from ~kings & from_mask to squares in target & to_mask
            //     (i.e., blocks or captures, but not with the king).
            {
                Bitboard new_from_mask = (~kings) & from_mask;
                Bitboard new_to_mask = target & to_mask;
                auto pseudo = generate_pseudo_legal_moves(new_from_mask, new_to_mask);
                moves.insert(moves.end(), pseudo.begin(), pseudo.end());
            }

            // 4c) If en-passant might capture the checker, handle that special case.
            if (ep_square >= 0)
            { // ep_square is valid
                // Check if ep-square is not in target
                if ((BB_SQUARES[ep_square] & target) == 0ULL)
                {
                    // The "checker" for en-passant would be the pawn that just moved 2 squares
                    int last_double = ep_square + (turn == WHITE ? -8 : 8);
                    if (last_double == checker_sq)
                    {
                        if (auto ep_moves_opt = generate_pseudo_legal_ep(from_mask, to_mask); ep_moves_opt)
                        {
                            moves.insert(moves.end(), ep_moves_opt->begin(), ep_moves_opt->end());
                        }
                    }
                }
            }
        }

        return moves;
    }

    Bitboard attackers_mask(Color color, Square square, std::optional<Bitboard> maybe_occupied = std::nullopt)
    {
        // Extract the actual bitboard, using `value_or()`:
        // Bitboard occupied = maybe_occupied.value_or(this->occupied);

        Bitboard rank_pieces = BB_RANK_MASKS[square] & occupied;
        Bitboard file_pieces = BB_FILE_MASKS[square] & occupied;
        Bitboard diag_pieces = BB_DIAG_MASKS[square] & occupied;

        Bitboard queens_and_rooks = queens | rooks;
        Bitboard queens_and_bishops = queens | bishops;

        Bitboard attackers = 0ULL;

        // King and knight attacks
        attackers |= (BB_KING_ATTACKS[square] & kings);
        attackers |= (BB_KNIGHT_ATTACKS[square] & knights);

        // Rank attacks
        {
            // look up rank_pieces key in BB_RANK_ATTACKS[square]
            auto it = BB_RANK_ATTACKS[square].find(rank_pieces);
            if (it != BB_RANK_ATTACKS[square].end())
            {
                // it->second is the attacked squares
                attackers |= (it->second & queens_and_rooks);
            }
        }

        // File attacks
        {
            auto it = BB_FILE_ATTACKS[square].find(file_pieces);
            if (it != BB_FILE_ATTACKS[square].end())
            {
                attackers |= (it->second & queens_and_rooks);
            }
        }

        // Diagonal attacks
        {
            auto it = BB_DIAG_ATTACKS[square].find(diag_pieces);
            if (it != BB_DIAG_ATTACKS[square].end())
            {
                attackers |= (it->second & queens_and_bishops);
            }
        }

        // Pawn attacks from the opposite color (Python uses `[not color][square]`):
        Color other = !color;
        attackers |= (BB_PAWN_ATTACKS[other][square] & pawns);

        // Only return the subset of attackers that actually belongs to <color>.
        // (Because we want pieces *of color* that can attack 'square'.)
        return attackers & occupied_co[color];
    }

    // Checks if the given pseudo-legal move is a castling move.
    bool is_castling(const Move &move) const
    {
        if (kings & BB_SQUARES[move.from_square])
        {
            int diff = square_file(move.from_square) - square_file(move.to_square);
            return (std::abs(diff) > 1) || static_cast<bool>(rooks & occupied_co[turn] & BB_SQUARES[move.to_square]);
        }
        return false;
    }

    bool is_attacked_by(Color color, Square square, std::optional<Bitboard> occupied = std::nullopt)
    {
        return static_cast<bool>(attackers_mask(color, square, occupied));
    }

    bool _is_safe(Square king, Bitboard blockers, Move move)
    {
        if (move.from_square == king)
        {
            if (is_castling(move))
            {
                return true;
            }
            else
            {
                return !is_attacked_by(!turn, move.to_square);
            }
        }
        else if (is_en_passant(move))
        {
            return (pin_mask(turn, move.from_square) & BB_SQUARES[move.to_square] &&
                    !_ep_skewered(king, move.from_square));
        }
        else
        {
            return (!(blockers & BB_SQUARES[move.from_square]) || (ray(move.from_square, move.to_square) & BB_SQUARES[king]));
        }
    }

    bool is_en_passant(const Move &move) const
    {
        // Bitboard for the from_square
        uint64_t from_square_bb = 1ULL << move.from_square;
        // Bitboard for the to_square
        uint64_t to_square_bb = 1ULL << move.to_square;

        // Check if the move is an en passant capture
        return (ep_square == move.to_square) &&
               (pawns & from_square_bb) &&                                                                               // Check if the moving piece is a pawn
               (std::abs(move.to_square - move.from_square) == 7 || std::abs(move.to_square - move.from_square) == 9) && // Check if the move is diagonal
               !(occupied & to_square_bb);                                                                               // Check if the target square is empty
    }

    Bitboard pin_mask(Color color, Square square)
    {
        // Find the square of our king. If none, return BB_ALL.
        std::optional<Square> king_sq = king(color);
        Bitboard king_sq_bb;
        if (!king_sq.has_value())
        {
            return BB_ALL;
        }
        else
        {
            king_sq_bb = king_sq.value();
        }

        // The single-bit mask of the piece whose pin we are checking
        Bitboard square_mask = BB_SQUARES[square];

        // We will check three directions: file, rank, diagonal
        // each with its corresponding slider set.
        // In Python you had: (BB_FILE_ATTACKS, rooks|queens), etc.
        // We'll store them in a small array or vector here:
        struct AttackSliders
        {
            std::vector<std::unordered_map<Bitboard, Bitboard>> &attacks;
            Bitboard slider_mask;
        };

        // NOTE: Adjust the type here to match how you store BB_FILE_ATTACKS etc.
        // For example, if they are declared as global arrays:
        // extern std::array<std::array<Bitboard, 512>, 64> BB_FILE_ATTACKS;
        // Then you'd need a matching type. This is just an illustration.

        std::vector<AttackSliders> combos = {
            {BB_FILE_ATTACKS, (rooks | queens)},
            {BB_RANK_ATTACKS, (rooks | queens)},
            {BB_DIAG_ATTACKS, (bishops | queens)}};

        // For each (attack_table, slider_bits)
        for (auto &combo : combos)
        {
            // In Python: `rays = attacks[king][0]`
            // Adjust if your table is used differently (like [king_sq][occupied_mask]).
            Bitboard rays = combo.attacks[king_sq_bb][0];

            // Check if the square in question is on these rays from the king.
            if ((rays & square_mask) != 0ULL)
            {
                // Potential snipers are the enemy long-range sliders
                Bitboard snipers = rays & combo.slider_mask & occupied_co[!color];
                // For each sniper from highest to lowest
                auto sniper_sqs = scan_reversed(snipers);
                for (int sniper_sq : sniper_sqs)
                {
                    // We'll see if exactly `square_mask` stands between the sniper and the king
                    // Note: (this->occupied | square_mask) is the union of all occupied squares plus the piece in question.
                    Bitboard blocks = between(sniper_sq, king_sq_bb) & (occupied | square_mask);

                    // If the squares in-between are exactly `square_mask`, meaning
                    // there's exactly one piece in the line (the piece at `square`) => pinned.
                    if (blocks == square_mask)
                    {
                        // Return the ray from king to sniper
                        return ray(king_sq_bb, sniper_sq);
                    }
                }
                // If we found no pinned piece in these directions, break out
                // of the loop (like "break" in Python).
                // The Python code breaks after the first direction that includes square_mask.
                break;
            }
        }

        // If no pin is found, return BB_ALL
        return BB_ALL;
    }

    bool _ep_skewered(int king, int capturer)
    {
        // 1) Ensure that we do have an en passant square.
        //    The Python code asserts `ep_square is not None`,
        //    so we can check ep_square >= 0 or throw/log an error.
        if (ep_square < 0)
        {
            return false;
        }

        // 2) Compute the 'last_double' square: The square of the pawn
        //    that just moved two squares and can be captured en passant.
        int last_double = ep_square + ((turn == WHITE) ? -8 : 8);

        // 3) Adjust occupancy:
        //    - Remove the pawn on last_double (the one that might be captured en passant).
        //    - Remove the capturing piece (as if it's no longer on the board).
        //    - Add a piece at ep_square (as if the capturing pawn has landed there).
        Bitboard occupancy = (occupied & ~BB_SQUARES[last_double] & ~BB_SQUARES[capturer]) | BB_SQUARES[ep_square];

        // 4) Check for horizontal (rank) attacks from opponent's rooks or queens.
        //    - The Python logic uses: BB_RANK_ATTACKS[king][BB_RANK_MASKS[king] & occ]
        //      then intersects with horizontal_attackers.
        //    - Adjust these lookups if your engine uses a different indexing scheme.

        Bitboard horizontal_attackers = occupied_co[!turn] & (rooks | queens);

        // Extract occupancy bits for rank attacks
        Bitboard rank_occ = BB_RANK_MASKS[king] & occupancy;
        // Look up the squares attacked by a rook horizontally from the king.
        // e.g.: Bitboard rank_attacks = BB_RANK_ATTACKS[king][rank_occ];
        // If your data is stored as `BB_RANK_ATTACKS[64][1<<8]`, you might need to do an integer index from `rank_occ`.
        // For demonstration we do exactly like Python: BB_RANK_ATTACKS[king][ rank_occ ]:

        Bitboard rank_attacks = BB_RANK_ATTACKS[king][rank_occ]; // Adjust if needed

        if (rank_attacks & horizontal_attackers)
        {
            return true;
        }

        // 5) Check for diagonal attacks from opponent's bishops or queens.
        //    The Python code suggests that in a real game it might be impossible,
        //    but let's do it anyway.

        Bitboard diagonal_attackers = occupied_co[!turn] & (bishops | queens);

        Bitboard diag_occ = BB_DIAG_MASKS[king] & occupancy;
        Bitboard diag_attacks = BB_DIAG_ATTACKS[king][diag_occ]; // Again, adjust indexing as needed

        if (diag_attacks & diagonal_attackers)
        {
            return true;
        }

        // 6) If we get here, there's no horizontal or diagonal skewer => false
        return false;
    }

    bool _attacked_for_king(Bitboard path, Bitboard occupied)
    {
        for (int sq : scan_reversed(path))
        {
            if (attackers_mask(!turn, sq, occupied))
            {
                return true;
            }
        }
        return false;
    }

    Bitboard attacks_mask(Square square)
    {
        Bitboard bb_square = BB_SQUARES[square];
        if (bb_square & pawns)
        {
            bool color = bool(bb_square & occupied_co[WHITE]);
            return BB_PAWN_ATTACKS[color][square];
        }
        else if (bb_square & knights)
        {
            return BB_KNIGHT_ATTACKS[square];
        }
        else if (bb_square & kings)
        {
            return BB_KING_ATTACKS[square];
        }
        else
        {
            Bitboard attacks = 0;
            if (bb_square & bishops or bb_square & queens)
            {
                attacks = BB_DIAG_ATTACKS[square][BB_DIAG_MASKS[square] & occupied];
            }
            if (bb_square & rooks or bb_square & queens)
            {
                attacks |= ((BB_RANK_ATTACKS[square][BB_RANK_MASKS[square] & occupied]) |
                            (BB_FILE_ATTACKS[square][BB_FILE_MASKS[square] & occupied]));
            }
            return attacks;
        }
    }

    Bitboard clean_castling_rights()
    {
        if (sizeof(_stack) >= 0)
        {
            return castling_rights;
        }

        bool castling = castling_rights & rooks;
        bool white_castling = castling & BB_RANK_1 & occupied_co[WHITE];
        bool black_castling = castling & BB_RANK_8 & occupied_co[BLACK];

        // The rooks must be on a1, h1, a8 or h8.
        white_castling &= (BB_A1 | BB_H1);
        black_castling &= (BB_A8 | BB_H8);

        // The kings must be on e1 or e8.
        if ((not occupied_co[WHITE]) & kings & ~promoted & BB_E1)
        {
            white_castling = 0;
        }
        if ((not occupied_co[BLACK]) & kings & ~promoted & BB_E8)
        {
            black_castling = 0;
        }

        return white_castling | black_castling;
    }

    std::vector<Move> generate_legal_moves(Bitboard from_mask = BB_ALL, Bitboard to_mask = BB_ALL)
    {
        // if (is_variant_end())
        // {
        //     std::vector<Move> none;
        //     return none;
        // }

        Bitboard king_mask = kings & occupied_co[turn];
        if (king_mask)
        {
            int king = msb(king_mask);
            auto blockers = _slider_blockers(king);
            auto checkers = attackers_mask(!turn, king);
            if (checkers)
            {
                std::vector<Move> moves;
                for (const auto &move : _generate_evasions(king, checkers, from_mask, to_mask))
                {
                    if (_is_safe(king, blockers, move))
                    {
                        moves.push_back(move);
                    }
                }
                return moves;
            }
            else
            {
                std::vector<Move> moves;
                for (const auto &move : generate_pseudo_legal_moves(from_mask, to_mask))
                {
                    if (_is_safe(king, blockers, move))
                    {
                        moves.push_back(move);
                    }
                }
                return moves;
            }
        }
        else
        {
            return generate_pseudo_legal_moves(from_mask, to_mask);
        }
    }

    std::optional<std::vector<Move>> generate_pseudo_legal_ep(Bitboard from_mask = BB_ALL, Bitboard to_mask = BB_ALL)
    {
        if (!ep_square || !(BB_SQUARES[ep_square] & to_mask))
        {
            return std::nullopt;
        }

        if (BB_SQUARES[ep_square] & occupied)
        {
            return std::nullopt;
        }

        Bitboard capturers = (pawns & occupied_co[turn] & from_mask &
                              BB_PAWN_ATTACKS[!turn][ep_square] &
                              BB_RANKS[turn ? 4 : 3]);

        std::vector<Move> moves;
        for (auto capturer : scan_reversed(capturers))
        {
            moves.push_back(Move(capturer, ep_square));
        }
        return moves;
    }

    Move _from_chess960(bool chess960, Square from_square, Square to_square, std::optional<PieceType> promotion = 0ULL, std::optional<PieceType> drop = 0ULL)
    {
        if (!chess960 and promotion == 0ULL and drop == 0ULL)
        {
            if (from_square == E1 and kings & BB_E1)
            {
                if (to_square == H1)
                {
                    return Move(E1, G1);
                }
                else if (to_square == A1)
                {
                    return Move(E1, C1);
                }
            }
            else if (from_square == E8 and kings & BB_E8)
            {
                if (to_square == H8)
                {
                    return Move(E8, G8);
                }
                else if (to_square == A8)
                {
                    return Move(E8, C8);
                }
            }
        }
        return Move(from_square, to_square, promotion.value(), drop.value());
    }

    std::vector<Move>
    generate_castling_moves(Bitboard from_mask /*= BB_ALL*/, Bitboard to_mask /*= BB_ALL*/)
    {
        std::vector<Move> moves;

        Bitboard backrank = (turn == WHITE ? BB_RANK_1 : BB_RANK_8);
        Bitboard king = (occupied_co[turn] & kings & ~promoted & backrank & from_mask);

        // 4) Keep only the lowest set bit
        //    king &= -king in Python
        if (king)
        {
            // isolate LSB. We can do the same trick:
            // Bitboard lsb_only = (king & (-(int64_t)king));
            king = lsb(king);
        }

        Bitboard bb_c = BB_FILE_C & backrank;
        Bitboard bb_d = BB_FILE_D & backrank;
        Bitboard bb_f = BB_FILE_F & backrank;
        Bitboard bb_g = BB_FILE_G & backrank;

        for (int candidate_sq : scan_reversed((clean_castling_rights() & backrank & to_mask)))
        {
            Bitboard rook_bb = BB_SQUARES[candidate_sq];

            // a_side = rook < king
            bool a_side = (candidate_sq < msb(king));
            Bitboard king_to = (a_side ? bb_c : bb_g);
            Bitboard rook_to = (a_side ? bb_d : bb_f);

            Bitboard king_path = between(msb(king), msb(rook_to));
            Bitboard rook_path = between(candidate_sq, msb(rook_to));

            if (((occupied ^ king ^ rook_bb) & (king_path | rook_path | king_to | rook_to)) != 0ULL)
            {
                continue;
            }
            if (_attacked_for_king(king_path | king, occupied ^ king))
            {
                continue;
            }
            if (_attacked_for_king(king_to, occupied ^ king ^ rook_bb ^ rook_to))
            {
                continue;
            }

            moves.push_back(_from_chess960(false, msb(king), candidate_sq));
        }

        return moves;
    }

    std::vector<Move> generate_pseudo_legal_moves(Bitboard from_mask /*= BB_ALL*/, Bitboard to_mask /*= BB_ALL*/)
    {
        std::vector<Move> moves;

        Bitboard our_pieces = occupied_co[turn];
        // Generate piece moves.
        Bitboard non_pawns = (our_pieces & ~pawns & from_mask);
        for (int from_square : scan_reversed(non_pawns))
        {
            Bitboard attacks = attacks_mask(from_square) & ~our_pieces & to_mask;
            for (int to_square : scan_reversed(attacks))
            {
                moves.emplace_back(Move(from_square, to_square));
            }
        }

        // Generate castling moves.
        if ((from_mask & kings) != 0ULL)
        {
            // yield from generate_castling_moves
            std::vector<Move> castling = generate_castling_moves(from_mask, to_mask);
            moves.insert(moves.end(), castling.begin(), castling.end());
        }

        // The remaining moves are all pawn moves.
        Bitboard our_pawns = (pawns & our_pieces & from_mask);
        if (our_pawns == 0ULL)
        {
            // No pawns -> just return what we have so far
            return moves;
        }

        // Generate pawn captures
        {
            // "capturers = our_pawns" (just a rename)
            Bitboard capturers = our_pawns;

            auto from_sqs = scan_reversed(capturers);
            for (int from_square : from_sqs)
            {
                Bitboard targets = BB_PAWN_ATTACKS[turn][from_square] & occupied_co[!turn] & to_mask;

                auto to_sqs = scan_reversed(targets);
                for (int to_square : to_sqs)
                {
                    int r = square_rank(to_square);
                    // If promotion rank
                    if (r == 0 || r == 7)
                    {
                        moves.emplace_back(Move(from_square, to_square, QUEEN));
                        moves.emplace_back(Move(from_square, to_square, ROOK));
                        moves.emplace_back(Move(from_square, to_square, BISHOP));
                        moves.emplace_back(Move(from_square, to_square, KNIGHT));
                    }
                    else
                    {
                        moves.emplace_back(Move(from_square, to_square));
                    }
                }
            }
        }

        // Prepare pawn advance generation.
        Bitboard single_moves = 0ULL, double_moves = 0ULL;
        if (turn == WHITE)
        {
            // White: shift pawns up
            single_moves = (our_pawns << 8) & ~occupied;
            double_moves = (single_moves << 8) & ~occupied & (BB_RANK_3 | BB_RANK_4);
        }
        else
        {
            // Black: shift pawns down
            single_moves = (our_pawns >> 8) & ~occupied;
            double_moves = (single_moves >> 8) & ~occupied & (BB_RANK_6 | BB_RANK_5);
        }

        // apply 'to_mask'
        single_moves &= to_mask;
        double_moves &= to_mask;

        // Generate single pawn moves.
        for (int to_square : scan_reversed(single_moves))
        {
            // from_square = to_square +/- 8
            int from_square = to_square + (turn == BLACK ? 8 : -8);

            int r = square_rank(to_square);
            if (r == 0 || r == 7)
            {
                // promotions
                moves.emplace_back(Move(from_square, to_square, QUEEN));
                moves.emplace_back(Move(from_square, to_square, ROOK));
                moves.emplace_back(Move(from_square, to_square, BISHOP));
                moves.emplace_back(Move(from_square, to_square, KNIGHT));
            }
            else
            {
                moves.emplace_back(Move(from_square, to_square));
            }
        }

        // Generate double pawn moves.
        for (int to_square : scan_reversed(double_moves))
        {
            int from_square = to_square + (turn == BLACK ? 16 : -16);
            moves.emplace_back(Move(from_square, to_square));
        }

        // 5) Generate en passant captures

        if (ep_square >= 0)
        {
            if (auto ep_captures = generate_pseudo_legal_ep(from_mask, to_mask); ep_captures)
            {
                moves.insert(moves.end(), ep_captures->begin(), ep_captures->end());
            }
        }

        // Return the full move list
        return moves;
    }

    //     Bitboard checkers_mask()
    //     {
    //         int local_king = king(turn).value();
    //         return (local_king == 0ULL) ? BB_EMPTY : attackers_mask(!turn, local_king);
    //     }

    //     bool is_check()
    //     {
    //         return bool(checkers_mask());
    //     }

    //     bool is_checkmate()
    //     {
    //         if (!is_check())
    //         {
    //             return false;
    //         }

    //         return (generate_legal_moves().size() == 0);
    //     }

    //     bool is_stalemate()
    //     {
    //         if (is_check())
    //         {
    //             return false;
    //         }

    //         if (is_variant_end())
    //         {
    //             return false;
    //         }
    //         return (generate_legal_moves().size() == 0);
    //     }

    //     bool has_insufficient_material(Color color)
    //     {
    //         if (occupied_co[color] & (pawns | rooks | queens))
    //         {
    //             return false;
    //         }

    //         if (occupied_co[color] & knights)
    //         {
    //             return ((popcount(occupied_co[color]) <= 2) && (!(occupied_co[not color] & ~kings & ~queens)));
    //         }
    //         if (occupied_co[color] & bishops)
    //         {
    //             bool same_color = ((!bishops) & BB_DARK_SQUARES) || ((!bishops) & BB_LIGHT_SQUARES);
    //             return same_color && (!pawns) && (!knights);
    //         }

    //         return true;
    //     }

    //     // legal_moves property
    //     LegalMoveGenerator
    //     get_legal_moves()
    //     {
    //         return LegalMoveGenerator(this);
    //     }
};

// // Implementation of LegalMoveGenerator methods
// std::vector<Move> LegalMoveGenerator::all_legal_moves()
// {
//     if (!board)
//         return {};
//     return board->generate_legal_moves();
// }

// int LegalMoveGenerator::count()
// {
//     auto v = all_legal_moves();
//     return (int)v.size();
// }

// bool LegalMoveGenerator::contains(const Move &move)
// {
//     auto v = all_legal_moves();
//     // check if `move` is in v
//     for (auto &m : v)
//     {
//         if (m.from_square == move.from_square &&
//             m.to_square == move.to_square &&
//             m.promotion == move.promotion &&
//             m.drop == move.drop)
//         {
//             return true;
//         }
//     }
//     return false;
// }

// // _BoardState Continued

// _BoardState::_BoardState(Board board)
// {
//     pawns = board.pawns;
//     knights = board.knights;
//     bishops = board.bishops;
//     rooks = board.rooks;
//     queens = board.queens;
//     kings = board.kings;

//     occupied_w = board.occupied_co[WHITE];
//     occupied_b = board.occupied_co[BLACK];
//     occupied = board.occupied;

//     promoted = board.promoted;

//     turn = board.turn;
//     castling_rights = board.castling_rights;
//     ep_square = board.ep_square;
//     halfmove_clock = board.halfmove_clock;
//     fullmove_number = board.fullmove_number;
// }

// void _BoardState::restore(Board board)
// {
//     board.pawns = pawns;
//     board.knights = knights;
//     board.bishops = bishops;
//     board.rooks = rooks;
//     board.queens = queens;
//     board.kings = kings;

//     board.occupied_co[WHITE] = occupied_w;
//     board.occupied_co[BLACK] = occupied_b;
//     board.occupied = occupied;

//     board.promoted = promoted;

//     board.turn = turn;
//     board.castling_rights = castling_rights;
//     board.ep_square = ep_square;
//     board.halfmove_clock = halfmove_clock;
//     board.fullmove_number = fullmove_number;
// }

std::string get_moves(char *fen)
{
    initialize_attack_tables();
    BB_RAYS = _rays();

    // Create a Board from the standard start
    std::string fen2 = fen;
    Board board(fen2);
    // Now we ask for legal moves:
    auto move_moves = board.generate_legal_moves();
    std::string moves = "";
    for (auto &move : move_moves)
    {
        moves += move.uci() + " ";
    }

    return moves;
}

// bool is_checkmate(std::string fen)
// {
//     return 0;
// }

// float calc_heuristic(std::string fen)
// {
//     return 0;
// }

// int main()
// {
//     char *fen = "rnbqkbnr/pp1ppppp/8/2p5/4P3/8/PPPP1PPP/RNBQKBNR w KQkq c6 0 2";
//     std::vector<std::string> moves = get_moves(fen);
//     for (auto move :moves){
//         std::cout << move << " ";
//     }
//     std::cout << std::endl;
// }

static PyObject *get_move(PyObject *self, PyObject *args)
{
    char *fen;

    // Parse the input arguments as strings (FEN and player color)
    if (!PyArg_ParseTuple(args, "s", &fen))
    {
        return NULL; // Error parsing arguments
    }

    // Get legal moves
    std::string moves = get_moves(fen);

    // Convert the result back to a Python string and return it
    return PyUnicode_FromString(moves.c_str());
}

static PyMethodDef methods[] = {
    {"get_move", get_move, METH_VARARGS, "Gets a chess move based on FEN and player color."},
    {NULL, NULL, 0}};

static struct PyModuleDef module = {
    PyModuleDef_HEAD_INIT,
    "my_extension",
    NULL,
    -1,
    methods};

PyMODINIT_FUNC PyInit_my_extension(void)
{
    return PyModule_Create(&module);
}
