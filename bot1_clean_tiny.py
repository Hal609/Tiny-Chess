_H='BB_E8'
_G='BB_E1'
_F='inf'
_E='E8'
_D='E1'
_C=True
_B=False
_A=None
import random,time
WHITE=_C
BLACK=_B
COLORS=[WHITE,BLACK]
PAWN=1
KNIGHT=2
BISHOP=3
ROOK=4
QUEEN=5
KING=6
PIECE_SYMBOLS=[_A,'p','n','b','r','q','k']
def piece_symbol(tpe):return str(PIECE_SYMBOLS[tpe])
FILE_NAMES=['a','b','c','d','e','f','g','h']
RANK_NAMES=['1','2','3','4','5','6','7','8']
SQUARES_DICT={str(chr(65+B))+str(A):A*8+B for A in range(1,9)for B in range(8)}
SQUARES=list(range(64))
SQUARE_NAMES=[B+A for A in RANK_NAMES for B in FILE_NAMES]
def square_file(square):return square&7
def square_rank(square):return square>>3
def square_distance(a,b):return max(abs(square_file(a)-square_file(b)),abs(square_rank(a)-square_rank(b)))
def square_mirror(square):return square^56
SQUARES_180=[square_mirror(A)for A in SQUARES]
BB_EMPTY=0
BB_ALL=0xffffffffffffffff
SQUARES_DICT={str(chr(65+B))+str(A):A*8+B for A in range(1,9)for B in range(8)}
BB_DICT={'BB_'+str(A):1<<B for(A,B)in SQUARES_DICT.items()}
BB_SQUARES=[1<<A for A in SQUARES]
BB_LIGHT_SQUARES=0x55aa55aa55aa55aa
BB_DARK_SQUARES=0xaa55aa55aa55aa55
BB_FL_A=72340172838076673
BB_FL_B=0x202020202020202
BB_FL_C=0x404040404040404
BB_FL_D=0x808080808080808
BB_FL_E=0x1010101010101010
BB_FL_F=0x2020202020202020
BB_FL_G=0x4040404040404040
BB_FL_H=0x8080808080808080
BB_FLS=[BB_FL_A,BB_FL_B,BB_FL_C,BB_FL_D,BB_FL_E,BB_FL_F,BB_FL_G,BB_FL_H]
BB_RK_1=255
BB_RK_2=65280
BB_RK_3=255<<16
BB_RK_4=255<<24
BB_RK_5=255<<32
BB_RK_6=255<<40
BB_RK_7=255<<48
BB_RK_8=255<<56
BB_RKS=[BB_RK_1,BB_RK_2,BB_RK_3,BB_RK_4,BB_RK_5,BB_RK_6,BB_RK_7,BB_RK_8]
BB_BACKRANKS=BB_RK_1|BB_RK_8
def lsb(bb):return(bb&-bb).bit_length()-1
def scan_forward(bb):
	while bb:A=bb&-bb;yield A.bit_length()-1;bb^=A
def msb(bb):return bb.bit_length()-1
def scan_reversed(bb):
	while bb:A=bb.bit_length()-1;yield A;bb^=BB_SQUARES[A]
popcount=getattr(int,'bit_count',lambda bb:bin(bb).count('1'))
def _sliding_attacks(square,occupied,deltas):
	B=BB_EMPTY
	for C in deltas:
		A=square
		while _C:
			A+=C
			if not 0<=A<64 or square_distance(A,A-C)>2:break
			B|=BB_SQUARES[A]
			if occupied&BB_SQUARES[A]:break
	return B
def _step_attacks(square,deltas):return _sliding_attacks(square,BB_ALL,deltas)
BB_KNIGHT_ATTACKS=[_step_attacks(A,[17,15,10,6,-17,-15,-10,-6])for A in SQUARES]
BB_KING_ATTACKS=[_step_attacks(A,[9,8,7,1,-9,-8,-7,-1])for A in SQUARES]
BB_PAWN_ATTACKS=[[_step_attacks(B,A)for B in SQUARES]for A in[[-7,-9],[7,9]]]
def _edges(square):A=square;return(BB_RK_1|BB_RK_8)&~BB_RKS[square_rank(A)]|(BB_FL_A|BB_FL_H)&~BB_FLS[square_file(A)]
def _carry_rippler(mask):
	A=BB_EMPTY
	while _C:
		yield A;A=A-mask&mask
		if not A:break
def _attack_table(deltas):
	B=deltas;C=[];D=[]
	for A in SQUARES:
		E={};F=_sliding_attacks(A,0,B)&~_edges(A)
		for G in _carry_rippler(F):E[G]=_sliding_attacks(A,G,B)
		D.append(E);C.append(F)
	return C,D
BB_DIAG_MASKS,BB_DIAG_ATTACKS=_attack_table([-9,-7,7,9])
BB_FL_MASKS,BB_FL_ATTACKS=_attack_table([-8,8])
BB_RK_MASKS,BB_RK_ATTACKS=_attack_table([-1,1])
def _rays():
	E=[]
	for(A,D)in enumerate(BB_SQUARES):
		B=[]
		for(F,C)in enumerate(BB_SQUARES):
			if BB_DIAG_ATTACKS[A][0]&C:B.append(BB_DIAG_ATTACKS[A][0]&BB_DIAG_ATTACKS[F][0]|D|C)
			elif BB_RK_ATTACKS[A][0]&C:B.append(BB_RK_ATTACKS[A][0]|D)
			elif BB_FL_ATTACKS[A][0]&C:B.append(BB_FL_ATTACKS[A][0]|D)
			else:B.append(BB_EMPTY)
		E.append(B)
	return E
BB_RAYS=_rays()
def ray(a,b):return BB_RAYS[a][b]
def between(a,b):A=BB_RAYS[a][b]&(BB_ALL<<a^BB_ALL<<b);return A&A-1
def from_symbol(symbol):A=symbol;return PIECE_SYMBOLS.index(A.lower()),A.isupper()
class Move:
	from_square:int;to_square:int;promotion=_A;drop=_A
	def __init__(A,from_sq,to_sq,prom=_A,drp=_A):A.from_square=from_sq;A.to_square=to_sq;A.promotion=prom;A.drop=drp
	def uci(A):
		if A.drop:return piece_symbol(A.drop).upper()+'@'+SQUARE_NAMES[A.to_square]
		elif A.promotion:return SQUARE_NAMES[A.from_square]+SQUARE_NAMES[A.to_square]+piece_symbol(A.promotion)
		elif A:return SQUARE_NAMES[A.from_square]+SQUARE_NAMES[A.to_square]
		else:return'0000'
	def __str__(A):return A.uci()
class BaseBoard:
	def __init__(A,board_fen):A.occupied_co=[BB_EMPTY,BB_EMPTY]
	def reset_board(A):A._reset_board()
	def _clear_board(A):A.pawns=BB_EMPTY;A.knights=BB_EMPTY;A.bishops=BB_EMPTY;A.rooks=BB_EMPTY;A.queens=BB_EMPTY;A.kings=BB_EMPTY;A.promoted=BB_EMPTY;A.occupied_co[WHITE]=BB_EMPTY;A.occupied_co[BLACK]=BB_EMPTY;A.occupied=BB_EMPTY
	def pieces_mask(A,tpe,color):
		B=tpe
		if B==PAWN:C=A.pawns
		elif B==KNIGHT:C=A.knights
		elif B==BISHOP:C=A.bishops
		elif B==ROOK:C=A.rooks
		elif B==QUEEN:C=A.queens
		elif B==KING:C=A.kings
		return C&A.occupied_co[color]
	def pieces(A,tpe,color):return intSet(A.pieces_mask(tpe,color))
	def tpe_at(A,square):
		B=BB_SQUARES[square]
		if not A.occupied&B:return
		elif A.pawns&B:return PAWN
		elif A.knights&B:return KNIGHT
		elif A.bishops&B:return BISHOP
		elif A.rooks&B:return ROOK
		elif A.queens&B:return QUEEN
		else:return KING
	def king(A,color):B=A.occupied_co[color]&A.kings&~A.promoted;return msb(B)if B else _A
	def attacks_mask(A,square):
		B=square;C=BB_SQUARES[B]
		if C&A.pawns:E=bool(C&A.occupied_co[WHITE]);return BB_PAWN_ATTACKS[E][B]
		elif C&A.knights:return BB_KNIGHT_ATTACKS[B]
		elif C&A.kings:return BB_KING_ATTACKS[B]
		else:
			D=0
			if C&A.bishops or C&A.queens:D=BB_DIAG_ATTACKS[B][BB_DIAG_MASKS[B]&A.occupied]
			if C&A.rooks or C&A.queens:D|=BB_RK_ATTACKS[B][BB_RK_MASKS[B]&A.occupied]|BB_FL_ATTACKS[B][BB_FL_MASKS[B]&A.occupied]
			return D
	def attackers_mask(A,color,square,occupied=_A):D=color;C=occupied;B=square;C=A.occupied if C is _A else C;F=BB_RK_MASKS[B]&C;G=BB_FL_MASKS[B]&C;H=BB_DIAG_MASKS[B]&C;E=A.queens|A.rooks;I=A.queens|A.bishops;J=BB_KING_ATTACKS[B]&A.kings|BB_KNIGHT_ATTACKS[B]&A.knights|BB_RK_ATTACKS[B][F]&E|BB_FL_ATTACKS[B][G]&E|BB_DIAG_ATTACKS[B][H]&I|BB_PAWN_ATTACKS[not D][B]&A.pawns;return J&A.occupied_co[D]
	def is_attacked_by(B,color,square,occupied=_A):A=occupied;return bool(B.attackers_mask(color,square,_A if A is _A else intSet(A).mask))
	def pin_mask(A,color,square):
		D=color;B=A.king(D)
		if B is _A:return BB_ALL
		C=BB_SQUARES[square]
		for(G,H)in[(BB_FL_ATTACKS,A.rooks|A.queens),(BB_RK_ATTACKS,A.rooks|A.queens),(BB_DIAG_ATTACKS,A.bishops|A.queens)]:
			E=G[B][0]
			if E&C:
				I=E&H&A.occupied_co[not D]
				for F in scan_reversed(I):
					if between(F,B)&(A.occupied|C)==C:return ray(B,F)
				break
		return BB_ALL
	def _remove_piece_at(A,square):
		D=square;C=A.tpe_at(D);B=BB_SQUARES[D]
		if C==PAWN:A.pawns^=B
		elif C==KNIGHT:A.knights^=B
		elif C==BISHOP:A.bishops^=B
		elif C==ROOK:A.rooks^=B
		elif C==QUEEN:A.queens^=B
		elif C==KING:A.kings^=B
		else:return
		A.occupied^=B;A.occupied_co[WHITE]&=~B;A.occupied_co[BLACK]&=~B;A.promoted&=~B;return C
	def _set_piece_at(A,square,tpe,color,promoted=_B):
		D=square;C=tpe;A._remove_piece_at(D);B=BB_SQUARES[D]
		if C==PAWN:A.pawns|=B
		elif C==KNIGHT:A.knights|=B
		elif C==BISHOP:A.bishops|=B
		elif C==ROOK:A.rooks|=B
		elif C==QUEEN:A.queens|=B
		elif C==KING:A.kings|=B
		else:return
		A.occupied^=B;A.occupied_co[color]^=B
		if promoted:A.promoted^=B
	def _set_board_fen(D,fen):
		B=fen;B=B.strip();H=B.split('/')
		for I in H:
			G=0;E=_B;F=_B
			for A in I:
				if A in['1','2','3','4','5','6','7','8']:G+=int(A);E=_C;F=_B
				elif A=='~':E=_B;F=_B
				elif A.lower()in PIECE_SYMBOLS:G+=1;E=_B;F=_C
		D._clear_board();C=0
		for A in B:
			if A in['1','2','3','4','5','6','7','8']:C+=int(A)
			elif A.lower()in PIECE_SYMBOLS:J,K=from_symbol(A);D._set_piece_at(SQUARES_180[C],J,K);C+=1
			elif A=='~':D.promoted|=BB_SQUARES[SQUARES_180[C-1]]
class _BoardState:
	def __init__(A,board):B=board;A.pawns=B.pawns;A.knights=B.knights;A.bishops=B.bishops;A.rooks=B.rooks;A.queens=B.queens;A.kings=B.kings;A.occupied_w=B.occupied_co[WHITE];A.occupied_b=B.occupied_co[BLACK];A.occupied=B.occupied;A.promoted=B.promoted;A.turn=B.turn;A.castling_rights=B.castling_rights;A.ep_square=B.ep_square;A.halfmove_clock=B.halfmove_clock;A.fullmove_number=B.fullmove_number
	def restore(A,board):B=board;B.pawns=A.pawns;B.knights=A.knights;B.bishops=A.bishops;B.rooks=A.rooks;B.queens=A.queens;B.kings=A.kings;B.occupied_co[WHITE]=A.occupied_w;B.occupied_co[BLACK]=A.occupied_b;B.occupied=A.occupied;B.promoted=A.promoted;B.turn=A.turn;B.castling_rights=A.castling_rights;B.ep_square=A.ep_square;B.halfmove_clock=A.halfmove_clock;B.fullmove_number=A.fullmove_number
class Board(BaseBoard):
	def __init__(A,fen,*,chess960=_B):
		BaseBoard.__init__(A,_A);A.chess960=chess960;A.ep_square=_A;A.move_stack=[];A._stack=[]
		if fen is _A:A.clear()
		else:A.set_fen(fen)
	@property
	def legal_moves(self):return LegalMoveGenerator(self)
	def clear_stack(A):A.move_stack.clear();A._stack.clear()
	def generate_pseudo_legal_moves(A,from_mask=BB_ALL,to_mask=BB_ALL):
		E=from_mask;D=to_mask;I=A.occupied_co[A.turn];J=I&~A.pawns&E
		for C in scan_reversed(J):
			K=A.attacks_mask(C)&~I&D
			for B in scan_reversed(K):yield Move(C,B)
		if E&A.kings:yield from A.generate_castling_moves(E,D)
		G=A.pawns&A.occupied_co[A.turn]&E
		if not G:return
		L=G
		for C in scan_reversed(L):
			M=BB_PAWN_ATTACKS[A.turn][C]&A.occupied_co[not A.turn]&D
			for B in scan_reversed(M):
				if square_rank(B)in[0,7]:yield Move(C,B,QUEEN);yield Move(C,B,ROOK);yield Move(C,B,BISHOP);yield Move(C,B,KNIGHT)
				else:yield Move(C,B)
		if A.turn==WHITE:F=G<<8&~A.occupied;H=F<<8&~A.occupied&(BB_RK_3|BB_RK_4)
		else:F=G>>8&~A.occupied;H=F>>8&~A.occupied&(BB_RK_6|BB_RK_5)
		F&=D;H&=D
		for B in scan_reversed(F):
			C=B+(8 if A.turn==BLACK else-8)
			if square_rank(B)in[0,7]:yield Move(C,B,QUEEN);yield Move(C,B,ROOK);yield Move(C,B,BISHOP);yield Move(C,B,KNIGHT)
			else:yield Move(C,B)
		for B in scan_reversed(H):C=B+(16 if A.turn==BLACK else-16);yield Move(C,B)
		if A.ep_square:yield from A.generate_pseudo_legal_ep(E,D)
	def generate_pseudo_legal_ep(A,from_mask=BB_ALL,to_mask=BB_ALL):
		if not A.ep_square or not BB_SQUARES[A.ep_square]&to_mask:return
		if BB_SQUARES[A.ep_square]&A.occupied:return
		B=A.pawns&A.occupied_co[A.turn]&from_mask&BB_PAWN_ATTACKS[not A.turn][A.ep_square]&BB_RKS[4 if A.turn else 3]
		for C in scan_reversed(B):yield Move(C,A.ep_square)
	def checkers_mask(A):B=A.king(A.turn);return BB_EMPTY if B is _A else A.attackers_mask(not A.turn,B)
	def is_check(A):return bool(A.checkers_mask())
	def gives_check(A,move):
		A.push(move)
		try:return A.is_check()
		finally:A.pop()
	def is_checkmate(A):
		if not A.is_check():return _B
		return not any(A.generate_legal_moves())
	def is_stalemate(A):
		if A.is_check():return _B
		return not any(A.generate_legal_moves())
	def is_insufficient_material(A):return all(A.has_insufficient_material(B)for B in COLORS)
	def has_insufficient_material(A,color):
		B=color
		if A.occupied_co[B]&(A.pawns|A.rooks|A.queens):return _B
		if A.occupied_co[B]&A.knights:return popcount(A.occupied_co[B])<=2 and not A.occupied_co[not B]&~A.kings&~A.queens
		if A.occupied_co[B]&A.bishops:C=not A.bishops&BB_DARK_SQUARES or not A.bishops&BB_LIGHT_SQUARES;return C and not A.pawns and not A.knights
		return _C
	def is_fivefold_repetition(A):return A.is_repetition(5)
	def is_repetition(A,count=3):
		B=count;C=1
		for F in reversed(A._stack):
			if F.occupied==A.occupied:
				C+=1
				if C>=B:break
		if C<B:return _B
		G=A._transposition_key();D=[]
		try:
			while _C:
				if B<=1:return _C
				if len(A.move_stack)<B-1:break
				E=A.pop();D.append(E)
				if A.is_irreversible(E):break
				if A._transposition_key()==G:B-=1
		finally:
			while D:A.push(D.pop())
		return _B
	def _push_capture(A,move,capture_square,tpe,was_promoted):0
	def push(A,move):
		B=move;B=A._to_chess960(B);L=_BoardState(A);A.castling_rights=A.clean_castling_rights();A.move_stack.append(A._from_chess960(A.chess960,B.from_square,B.to_square,B.promotion,B.drop));A._stack.append(L);I=A.ep_square;A.ep_square=_A;A.halfmove_clock+=1
		if A.turn==BLACK:A.fullmove_number+=1
		if not B:A.turn=not A.turn;return
		if B.drop:A._set_piece_at(B.to_square,B.drop,A.turn);A.turn=not A.turn;return
		if A.is_zeroing(B):A.halfmove_clock=0
		J=BB_SQUARES[B.from_square];E=BB_SQUARES[B.to_square];G=bool(A.promoted&J);C=A._remove_piece_at(B.from_square);F=B.to_square;D=A.tpe_at(F);A.castling_rights&=~E&~J
		if C==KING and not G:
			if A.turn==WHITE:A.castling_rights&=~BB_RK_1
			else:A.castling_rights&=~BB_RK_8
		elif D==KING and not A.promoted&E:
			if A.turn==WHITE and square_rank(B.to_square)==7:A.castling_rights&=~BB_RK_8
			elif A.turn==BLACK and square_rank(B.to_square)==0:A.castling_rights&=~BB_RK_1
		if C==PAWN:
			H=B.to_square-B.from_square
			if H==16 and square_rank(B.from_square)==1:A.ep_square=B.from_square+8
			elif H==-16 and square_rank(B.from_square)==6:A.ep_square=B.from_square-8
			elif B.to_square==I and abs(H)in[7,9]and not D:M=-8 if A.turn==WHITE else 8;F=I+M;D=A._remove_piece_at(F)
		if B.promotion:G=_C;C=B.promotion
		K=C==KING and A.occupied_co[A.turn]&E
		if K:
			N=square_file(B.to_square)<square_file(B.from_square);A._remove_piece_at(B.from_square);A._remove_piece_at(B.to_square)
			if N:A._set_piece_at(SQUARES_DICT['C1']if A.turn==WHITE else SQUARES_DICT[' 8'],KING,A.turn);A._set_piece_at(SQUARES_DICT['D1']if A.turn==WHITE else SQUARES_DICT['D8'],ROOK,A.turn)
			else:A._set_piece_at(SQUARES_DICT['G1']if A.turn==WHITE else SQUARES_DICT['G8'],KING,A.turn);A._set_piece_at(SQUARES_DICT['F1']if A.turn==WHITE else SQUARES_DICT['F8'],ROOK,A.turn)
		if not K:
			O=bool(A.promoted&E);A._set_piece_at(B.to_square,C,A.turn,G)
			if D:A._push_capture(B,F,D,O)
		A.turn=not A.turn
	def pop(A):B=A.move_stack.pop();A._stack.pop().restore(A);return B
	def set_fen(A,fen):B=fen.split();E=B.pop(0);F=B.pop(0);G=WHITE if F=='w'else BLACK;H=B.pop(0);D=B.pop(0);I=_A if D=='-'else SQUARE_NAMES.index(D);J=B.pop(0);K=int(J);L=B.pop(0);C=int(L);C=max(C,1);A._set_board_fen(E);A.turn=G;A._set_castling_fen(H);A.ep_square=I;A.halfmove_clock=K;A.fullmove_number=C;A.clear_stack()
	def _set_castling_fen(A,castling_fen):
		F=castling_fen
		if not F or F=='-':A.castling_rights=BB_EMPTY;return
		A.castling_rights=BB_EMPTY
		for B in F:
			G=WHITE if B.isupper()else BLACK;B=B.lower();C=BB_RK_1 if G==WHITE else BB_RK_8;D=A.occupied_co[G]&A.rooks&C;E=A.king(G)
			if B=='q':
				if E is not _A and lsb(D)<E:A.castling_rights|=D&-D
				else:A.castling_rights|=BB_FL_A&C
			elif B=='k':
				H=msb(D)
				if E is not _A and E<H:A.castling_rights|=BB_SQUARES[H]
				else:A.castling_rights|=BB_FL_H&C
			else:A.castling_rights|=BB_FLS[FILE_NAMES.index(B)]&C
	def is_en_passant(B,move):A=move;return B.ep_square==A.to_square and bool(B.pawns&BB_SQUARES[A.from_square])and abs(A.to_square-A.from_square)in[7,9]and not B.occupied&BB_SQUARES[A.to_square]
	def is_capture(A,move):B=move;C=BB_SQUARES[B.from_square]^BB_SQUARES[B.to_square];return bool(C&A.occupied_co[not A.turn])or A.is_en_passant(B)
	def is_zeroing(A,move):B=move;C=BB_SQUARES[B.from_square]^BB_SQUARES[B.to_square];return bool(C&A.pawns or C&A.occupied_co[not A.turn]or B.drop==PAWN)
	def is_castling(A,move):
		B=move
		if A.kings&BB_SQUARES[B.from_square]:C=square_file(B.from_square)-square_file(B.to_square);return abs(C)>1 or bool(A.rooks&A.occupied_co[A.turn]&BB_SQUARES[B.to_square])
		return _B
	def clean_castling_rights(A):
		if A._stack:return A.castling_rights
		J=A.castling_rights&A.rooks;B=J&BB_RK_1&A.occupied_co[WHITE];C=J&BB_RK_8&A.occupied_co[BLACK]
		if not A.chess960:
			B&=BB_DICT['BB_A1']|BB_DICT['BB_H1'];C&=BB_DICT['BB_A8']|BB_DICT['BB_H8']
			if not A.occupied_co[WHITE]&A.kings&~A.promoted&BB_DICT[_G]:B=0
			if not A.occupied_co[BLACK]&A.kings&~A.promoted&BB_DICT[_H]:C=0
			return B|C
		else:
			H=A.occupied_co[WHITE]&A.kings&BB_RK_1&~A.promoted;I=A.occupied_co[BLACK]&A.kings&BB_RK_8&~A.promoted
			if not H:B=0
			if not I:C=0
			D=B&-B;E=BB_SQUARES[msb(B)]if B else 0
			if D and msb(D)>msb(H):D=0
			if E and msb(E)<msb(H):E=0
			F=C&-C;G=BB_SQUARES[msb(C)]if C else BB_EMPTY
			if F and msb(F)>msb(I):F=0
			if G and msb(G)<msb(I):G=0
			return F|G|D|E
	def _ep_skewered(A,king,capturer):
		B=king;assert A.ep_square is not _A;D=A.ep_square+(-8 if A.turn==WHITE else 8);C=A.occupied&~BB_SQUARES[D]&~BB_SQUARES[capturer]|BB_SQUARES[A.ep_square];E=A.occupied_co[not A.turn]&(A.rooks|A.queens)
		if BB_RK_ATTACKS[B][BB_RK_MASKS[B]&C]&E:return _C
		F=A.occupied_co[not A.turn]&(A.bishops|A.queens)
		if BB_DIAG_ATTACKS[B][BB_DIAG_MASKS[B]&C]&F:return _C
		return _B
	def _slider_blockers(A,king):
		B=king;D=A.rooks|A.queens;F=A.bishops|A.queens;G=BB_RK_ATTACKS[B][0]&D|BB_FL_ATTACKS[B][0]&D|BB_DIAG_ATTACKS[B][0]&F;E=0
		for H in scan_reversed(G&A.occupied_co[not A.turn]):
			C=between(B,H)&A.occupied
			if C and BB_SQUARES[msb(C)]==C:E|=C
		return E&A.occupied_co[A.turn]
	def _is_safe(B,king,blockers,move):
		C=king;A=move
		if A.from_square==C:
			if B.is_castling(A):return _C
			else:return not B.is_attacked_by(not B.turn,A.to_square)
		elif B.is_en_passant(A):return bool(B.pin_mask(B.turn,A.from_square)&BB_SQUARES[A.to_square]and not B._ep_skewered(C,A.from_square))
		else:return bool(not blockers&BB_SQUARES[A.from_square]or ray(A.from_square,A.to_square)&BB_SQUARES[C])
	def _generate_evasions(A,king,checkers,from_mask=BB_ALL,to_mask=BB_ALL):
		F=to_mask;E=from_mask;D=checkers;C=king;I=D&(A.bishops|A.rooks|A.queens);G=0
		for B in scan_reversed(I):G|=ray(C,B)&~BB_SQUARES[B]
		if BB_SQUARES[C]&E:
			for J in scan_reversed(BB_KING_ATTACKS[C]&~A.occupied_co[A.turn]&~G&F):yield Move(C,J)
		B=msb(D)
		if BB_SQUARES[B]==D:
			H=between(C,B)|D;yield from A.generate_pseudo_legal_moves(~A.kings&E,H&F)
			if A.ep_square and not BB_SQUARES[A.ep_square]&H:
				K=A.ep_square+(-8 if A.turn==WHITE else 8)
				if K==B:yield from A.generate_pseudo_legal_ep(E,F)
	def generate_legal_moves(A,from_mask=BB_ALL,to_mask=BB_ALL):
		E=to_mask;D=from_mask;F=A.kings&A.occupied_co[A.turn]
		if F:
			B=msb(F);G=A._slider_blockers(B);H=A.attackers_mask(not A.turn,B)
			if H:
				for C in A._generate_evasions(B,H,D,E):
					if A._is_safe(B,G,C):yield C
			else:
				for C in A.generate_pseudo_legal_moves(D,E):
					if A._is_safe(B,G,C):yield C
		else:yield from A.generate_pseudo_legal_moves(D,E)
	def generate_castling_moves(A,from_mask=BB_ALL,to_mask=BB_ALL):
		C=BB_RK_1 if A.turn==WHITE else BB_RK_8;B=A.occupied_co[A.turn]&A.kings&~A.promoted&C&from_mask;B&=-B
		if not B:return
		J=BB_FL_C&C;K=BB_FL_D&C;L=BB_FL_F&C;M=BB_FL_G&C
		for D in scan_reversed(A.clean_castling_rights()&C&to_mask):
			E=BB_SQUARES[D];H=E<B;F=J if H else M;G=K if H else L;I=between(msb(B),msb(F));N=between(D,msb(G))
			if not((A.occupied^B^E)&(I|N|F|G)or A._attacked_for_king(I|B,A.occupied^B)or A._attacked_for_king(F,A.occupied^B^E^G)):yield A._from_chess960(A.chess960,msb(B),D)
	def _from_chess960(C,chess960,from_square,to_square,promotion=_A,drop=_A):
		D=promotion;B=from_square;A=to_square
		if not chess960 and D is _A and drop is _A:
			if B==SQUARES_DICT[_D]and C.kings&BB_DICT[_G]:
				if A==SQUARES_DICT['H1']:return Move(SQUARES_DICT[_D],SQUARES_DICT['G1'])
				elif A==SQUARES_DICT['A1']:return Move(SQUARES_DICT[_D],SQUARES_DICT['C1'])
			elif B==SQUARES_DICT[_E]and C.kings&BB_DICT[_H]:
				if A==SQUARES_DICT['H8']:return Move(SQUARES_DICT[_E],SQUARES_DICT['G8'])
				elif A==SQUARES_DICT['A8']:return Move(SQUARES_DICT[_E],SQUARES_DICT['C8'])
		return Move(B,A,D,drop)
	def _to_chess960(B,move):
		A=move
		if A.from_square==SQUARES_DICT[_D]and B.kings&BB_DICT[_G]:
			if A.to_square==SQUARES_DICT['G1']and not B.rooks&BB_DICT['BB_G1']:return Move(SQUARES_DICT[_D],SQUARES_DICT['H1'])
			elif A.to_square==SQUARES_DICT['C1']and not B.rooks&BB_DICT['BB_C1']:return Move(SQUARES_DICT[_D],SQUARES_DICT['A1'])
		elif A.from_square==SQUARES_DICT[_E]and B.kings&BB_DICT[_H]:
			if A.to_square==SQUARES_DICT['G8']and not B.rooks&BB_DICT['BB_G8']:return Move(SQUARES_DICT[_E],SQUARES_DICT['H8'])
			elif A.to_square==SQUARES_DICT['C8']and not B.rooks&BB_DICT['BB_C8']:return Move(SQUARES_DICT[_E],SQUARES_DICT['A8'])
		return A
class LegalMoveGenerator:
	def __init__(A,board):A.board=board
	def __iter__(A):return A.board.generate_legal_moves()
class intSet:
	def __init__(A,squares=BB_EMPTY):A.mask=squares.__int__()&BB_ALL
	def __iter__(A):return scan_forward(A.mask)
	def __len__(A):return popcount(A.mask)
def calc_heuristic(state):
	A=state
	if A.is_checkmate():return(A.turn*2-1)*-float(_F)
	if A.is_stalemate()or A.is_insufficient_material()or A.is_fivefold_repetition():return 0
	B=0;E=[1,2,3,4,5,3,2,1]
	for(F,P)in{PAWN:1,KNIGHT:3,BISHOP:3,ROOK:5,QUEEN:9}.items():
		M=A.pieces(F,WHITE);N=A.pieces(F,BLACK);B+=P*(len(M)-len(N))
		if F==PAWN:
			for C in M:
				D=square_rank(C);G=square_file(C);B+=.1*E[G]*(D-1)
				if D==8:B+=6
			for C in N:
				D=square_rank(C);G=square_file(C);B-=.1*E[G]*(6-D)
				if D==0:B-=6
	H=A.king(WHITE);I=A.king(BLACK)
	if H is not _A:Q=square_rank(H);R=square_file(H);B+=.5*(.2*E[R]-Q)
	if I is not _A:S=square_rank(I);T=square_file(I);B+=.5*(.2*E[T]+(7-S))
	U={KNIGHT:{1,6},BISHOP:{2,5},ROOK:{0,7},QUEEN:{3},KING:{4}};V={KNIGHT:{57,62},BISHOP:{58,61},ROOK:{56,63},QUEEN:{59},KING:{60}};O=.1
	for(J,K)in U.items():
		for L in A.pieces(J,WHITE):
			if L in K:B-=O
	for(J,K)in V.items():
		for L in A.pieces(J,BLACK):
			if L in K:B+=O
	return B
def minimax(state,depth,alpha,beta,maximizingPlayer):
	J=depth;H=maximizingPlayer;C=beta;B=alpha;A=state;global start_time,time_limit
	if time.time()-start_time>time_limit or J==0:return calc_heuristic(A),_A
	D=_A;K=list(A.legal_moves)
	def L(move):return A.is_capture(move)+.5*A.gives_check(move)+.01*random.random()
	K.sort(key=L,reverse=_C);E=-float(_F);F=float(_F)
	for I in K:
		A.push(I);G,M=minimax(A,J-1,B,C,not H);A.pop()
		if H:
			if G>E:E=G;D=I
			B=max(B,E)
		else:
			if G<F:F=G;D=I
			C=min(C,F)
		if C<=B:break
	return(E,D)if H else(F,D)
start_time:0
time_limit:0
max_depth=3
def chess_bot(obs):
	H='e8b8';G='e8g8';F='e1b1';E='e1g1';global start_time,time_limit,max_depth;B=Board(obs.board);A=[A.uci()for A in B.legal_moves];start_time=time.time();C=obs['remainingOverageTime'];time_limit=.09 if C>2 else C/5
	if not A:return'resign'
	if C<=.1:return random.choice(A)
	if E in A:return E
	if F in A:return F
	if G in A:return G
	if H in A:return H
	I,D=minimax(B,depth=max_depth,alpha=-float(_F),beta=float(_F),maximizingPlayer=B.turn)
	if D is _A:D=random.choice(A)
	return str(D)