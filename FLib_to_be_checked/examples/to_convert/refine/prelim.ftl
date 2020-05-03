[read refine/sets.ftl]

[a state/states]
[the domain of x] [Dom f @ the domain of f]
[f : x @ f is a state such that Dom f = x]
[the restriction of f to x] [f ! x @ the restriction of f to x]
[the sum of f and g] [f ++ g @ the sum of f and g]
[the over of f and g] [f -+ g @ the over of f and g]
[f coincides/coincide with g on x @ f!x = g!x]

Axiom DomSet. The domain of every state is a set.

Axiom DomRst.  For every state F and every set A  (F!A) : (A*Dom F).

Lemma RstStt. The restriction of every state to every set is a state.

Lemma RstSub. For every state F and every A <= Dom F  (F!A) : A (by InSub,DomRst).

Axiom RstDom.  For every state F and every set A
                    if Dom F <= A then (F!A) = F.

Axiom RstRst.  For every state F and every set A
                    for every B <= A  (F!A)!B = F!B.

Definition DefSum.  Let F,G be states that coincide on Dom F * Dom G.
    F ++ G is a state H such that Dom H = Dom F + Dom G
        and H,F coincide on Dom F and H,G coincide on Dom G.

Definition DefOver. Let F,G be states.
    F -+ G is a state H such that Dom H = Dom F + Dom G
        and H,F coincide on (Dom H - Dom G) and H,G coincide on Dom G.

Axiom CoinUn.  Let F,G be states and A,B be sets.
    If F,G coincide on A and coincide on B then F,G coincide on A + B.


[a substitution/substitutions]
[the variables of x] [Var x @ the variables of x]
[the modifiables of x] [Mod x @ the modifiables of x]
[the persistents of x] [Per x @ persistents of x]

Axiom ModSet.  The modifiables of every substitution is a set.
Axiom PerSet.  The persistents of every substitution is a set.

Axiom ModPer.   For every substitution S    Per S !! Mod S.

Definition DefVar.  Let S be a substitution.
    Var S is Mod S + Per S.

Lemma VarSet.   The variables of every substitution is a set.
Lemma ModVar.   For every substitution S  Mod S = Var S - Per S.
Lemma PerVar.   For every substitution S  Per S = Var S - Mod S.


[x terminates/terminate in y] [x -| y @ x terminates in y]
[x narrowly moves/move y to z] [x :: y >> z @ x narrowly moves y to z]
[x broadly moves/move y to z]  [x :: y ->> z @ x broadly moves y to z]
[x moves/move y to z]  [x :: y -> z @ x moves y to z]

Definition DefMove.   Let S be a substitution and F,G : Var S.
    S :: F -> G iff S :: F >> G and F,G coincide on Per S.

Definition DefBMove.  Let S be a substitution and F,G be states.
    Assume Dom F = Dom G and Var S <= Dom F.
    S :: F ->> G iff S :: (F!Var S) -> (G!Var S)
        and F,G coincide on (Dom F - Var S).


[an invariant/invariants]
[x glues/glue y to z] [x(y,z) @ x glues y to z]
[x refines/refine y wrt z] [x [z= y @ y refines x wrt z]

Definition DefRef.
    Let S,T be substitutions and J be an invariant.
    S [J= T iff
#        (for some F : Var S and some G : Var T  J(F,G)) and
        for all F : Var S and all G : Var T
            if (S -| F) and J(F, G) then (T -| G)
            and for every I : Var T such that T :: G -> I
                there exists H : Var S such that S :: F -> H and J(H,I).


