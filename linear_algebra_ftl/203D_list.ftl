[read linear_algebra_ftl/A_Props/201A_subspace.ftl]

[synonym List/-s]

Signature.
A List is a function.

Definition. A liststr is a structure K such that (K has carr, zero)  
 and (|K| is a set) 
 and (0{K} < K).

Signature.
Assume L is a list.
B(L) is a set.

Signature.
Assume L is a list.
str(L) is a liststr.

Axiom.
Let L be a List.
L is from B(L) to |str(L)|.

Signature.
Assume L be a List.
Assume f is a function from Prod(|str(L)|,|str(L)|) to |str(L)|.
listsum(L, f) is an element of |str(L)|.

Axiom.
Assume L be a List.
Assume f is a function from Prod(|str(L)|,|str(L)|) to |str(L)|.
Assume B(L) has no elements.
listsum(L, f) = 0{str(L)}.

Axiom.
Assume L be a List.
Assume f is a function from Prod(|str(L)|,|str(L)|) to |str(L)|.
Assume f[(0{str(L)}, 0{str(L)})] = 0{str(L)}.
Assume for all z<<B(L) L[z] = 0{str(L)}.
listsum(L, f) = 0{str(L)}.

Definition.
Assume L be a List.
Assume K be a List.
Assume B(L) = B(K).
Assume f is a function from Prod(|str(L)|,|str(K)|) to |str(K)|.
listmul(L, K, f) is a List R such that
      B(R) = B(K)
      and str(R) = str(K)
      and for all z << B(R) R[z] = f[(L[z], K[z])].

Definition.
Assume L be a List.
Let a << B(L).
cut(L,a) is a List R such that
    B(R) = {x | x << B(L) and x != a}
    and str(R) = str(L)
    and for all z << B(R) R[z] = L[z].

Definition.
Assume L be a List.
Let a be an object.
Assume a is not an element of B(L).
Assume n << |str(L)|.
add(L,a,n) is a List R such that
    (B(R) = {x | x << B(L) or x = a})
    and (str(R) = str(L))
    and (for all z << B(L) R[z] = L[z])
    and (R[a] = n).

Axiom listsumind.
Assume L be a List.
Assume f is a function from Prod(|str(L)|,|str(L)|) to |str(L)|.
Assume B(L) has an element.
Let a << B(L).
Assume T be a List.
Assume B(T) = B(L) and str(T) = str(L).
Assume for all c << B(L) such that c != a T[c] = L[c].
Assume L[a] = 0{str(L)}.
Then f[(listsum(L,f),T[a])] = listsum(T,f).


Definition.
Assume L be a List.
A sublist over L is a List K such that
  (str(K) = str(L))
  and (B(K) is subset of B(L))
  and (L|{B(K)} = K).
