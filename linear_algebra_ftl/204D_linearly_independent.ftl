[read linear_algebra_ftl/A_Props/203A_list.ftl]

Definition.
Assume L be a List. Assume T be a List.
Assume B(L) = B(T).
Assume K is a field. Assume V is a vector space over K.
Assume str(L) = K. Assume str(T) = V.
listvmul(L,T,K,V) = listmul(L,T,V[smul]).

Definition.
Assume L be a List. Assume T be a List.
Assume B(L) = B(T).
Assume K is a field. Assume V is a vector space over K.
Assume str(L) = V. Assume str(T) = V.
listvadd(L,T,K,V) = listmul(L,T,V[add]).

Definition.
Assume L be a List. Assume T be a List.
Assume B(L) = B(T).
Assume K is a field. Assume V is a vector space over K.
Assume str(L) = K. Assume str(T) = V.
lincomb(L,T,K,V) is an element t of |str(T)| such that t = listsum((listvmul(L,T,K,V)),(V[add])).

Definition.
Assume L be a List.
Assume K is a field. Assume V is a vector space over K.
Assume str(L) = V.
L is linearly independent over K and V iff 
  (for every List T such that 
  (B(T) = B(L) and str(T) = K and there exists a << B(T) such that T[a] != 0{str(T)})
  lincomb(T,L,K,V) = 0{str(L)}).

Axiom.
Assume L be a List.
Assume f is a function from Prod(|str(L)|,|str(L)|) to |str(L)|.
Assume f[(0{str(L)}, 0{str(L)})] = 0{str(L)}.
Assume for all z<<B(L) L[z] = 0{str(L)}.
listsum(L, f) = 0{str(L)}.
 