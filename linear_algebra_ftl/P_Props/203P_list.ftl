[read linear_algebra_ftl/203D_list.ftl]

Theorem.
Assume L be a List.
Assume |str(L)| has an element.
Let a << B(L).
add(cut(L,a),a,L[a]) = L.
proof.
  Let us show that B(add(cut(L,a),a,L[a])) = B(L).
    B(L) is a set.
    B(add(cut(L,a),a,L[a])) is a set.
    let us show that for all  b << B(add(cut(L,a),a,L[a])) b << B(L).
      Let b << B(add(cut(L,a),a,L[a])).
      b << B(cut(L,a)) or b=a.
      if b = a then b << B(L).
      if b << B(cut(L,a)) then b << B(L).
    end.
    let us show that for all  b << B(L) b << B(add(cut(L,a),a,L[a])).
      Let b << B(L).
      b << B(cut(L,a)) or b=a.
      if b = a then b << B(L).
      if b << B(cut(L,a)) then b << B(L).
    end.
    Hence the thesis (by SetEq).
  end.
  str(add(cut(L,a),a,L[a])) = str(L).
  Let us show that for all b << B(add(cut(L,a),a,L[a])) add(cut(L,a),a,L[a])[b] = L[b].
    Let b << B(add(cut(L,a),a,L[a])).
    b << B(cut(L,a)) or b=a.
    if b << B(cut(L,a)) then add(cut(L,a),a,L[a])[b] = L[b].
    if b = a then add(cut(L,a),a,L[a])[a] = L[a].
  end.
end.