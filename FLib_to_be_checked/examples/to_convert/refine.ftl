[a set/sets] [the empty set] [{} @ the empty set]
[a subset/subsets of x] [x <= y @ x is a subset of y]
[the union of x and y] [x + y @ the union of x and y]
[the intersection of x and y] [x * y @ the intersection of x and y]
[the complement of x to y] [y - x @ the complement of x to y]
[x is disjoint with y @ x * y = {}] [x !! y @ x is disjoint with y]

Axiom EmSet.   {} is a set.
Axiom SubSet.  Every subset of every set is a set.

Axiom _ReflSub. For every set A     A <= A.
Axiom AsymSub.  For all sets A,B    A <= B /\ B <= A => A = B.
Axiom TranSub.  For all sets A,B,C  A <= B /\ B <= C => A <= C.

Axiom UnSet.   For all sets A,B    A + B is a set.
Axiom InSet.   For all sets A,B    A * B is a set.
Axiom CmSet.   For all sets A,B    A - B is a set.

Axiom _IdemUn.  For every set A     A + A = A.
Axiom _IdemIn.  For every set A     A * A = A.
Axiom _UnEmpty. For every set A     A + {} = A /\ {} + A = A.
Axiom _InEmpty. For every set A     A * {} = {} /\ {} * A = {}.
Axiom _SubsmUn. For all sets A,B    A + (A * B) = A.
Axiom _SubsmIn. For all sets A,B    A * (A + B) = A.

Axiom _SubUn.   For all sets A,B    A <= A + B /\ B <= A + B.
Axiom _SubIn.   For all sets A,B    A * B <= A /\ A * B <= B.
Axiom _SubCm.   For all sets A,B    A - B <= A.

Axiom CommUn.   For all sets A,B    A + B = B + A.
Axiom CommIn.   For all sets A,B    A * B = B * A.
Axiom AssoUn.   For all sets A,B,C  (A + B) + C = A + (B + C).
Axiom AssoIn.   For all sets A,B,C  (A * B) * C = A * (B * C).
Axiom DistLUn.  For all sets A,B,C  A + (B * C) = (A + B) * (A + C).
Axiom DistLIn.  For all sets A,B,C  A * (B + C) = (A * B) + (A * C).
Axiom DistRUn.  For all sets A,B,C  (A * B) + C = (A + C) * (B + C).
Axiom DistRIn.  For all sets A,B,C  (A + B) * C = (A * C) + (B * C).
Axiom UnSub.    For all sets A,B    A <= B <=> A + B = B.
Axiom InSub.    For all sets A,B    A <= B <=> A * B = A.
Axiom CmCm.     For all sets A,B    A - (A - B) = A * B.
Axiom CmDj.     For all sets A,B    A !! B  <=>  (A + B) - A = B.
Axiom DjUn.     For all sets A,B,C  A !! B /\ A !! C  <=>  A !! (B + C).
Axiom DjCm.     For all sets A,B,C  A !! B /\ A <= C => A <= C - B.
Axiom UnCm.     For all sets A,B    (A + B) - A = B - A.
Axiom DuCm.     For all sets A,B    A !! B  =>  A - B = A.


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


[the parcomp of s and t] [s || t @ the parcomp of s and t]
[s is compatible with t @ Mod s !! Mod t]

Axiom PCWF.
    For all compatible substitutions S,T  (S || T) is a substitution.

Axiom PCMod.
    For all compatible substitutions S,T  Mod (S || T) = Mod S + Mod T.

Axiom PCVar.
    For all compatible substitutions S,T  Var (S || T) = Var S + Var T.

Axiom PCTerm.   Let S,T be compatible substitutions and F : Var (S||T).
    S || T -| F  <=>  S -| (F ! Var S) /\ T -| (F ! Var T).

Axiom PCMove.  Let S,T be compatible substitutions and F,G : Var (S||T).
    S || T :: F -> G  <=>   S :: (F ! Var S) >> (G ! Var S)
                        /\  T :: (F ! Var T) >> (G ! Var T)
                        /\  (F,G coincide on Per (S || T)).


Theorem ReusePC.
    Let S,T,U,V be substitutions and L,M,J be invariants.
    Assume S,U are compatible and T,V are compatible.
    Assume S [L= T and U [M= V.
    Then (S||U) [J= (T||V) (by _). # (by DefRefB).
Proof.
    S||U and T||V are substitutions. ## BAD
    Let F : Var (S||U) and G : Var (T||V).
    Assume (S||U) -| F and J(F, G).

    Var S <= Dom F and Var U <= Dom F. # (by PCVar).
    Var T <= Dom G and Var V <= Dom G. # (by PCVar).
    (F!Var S) : Var S and (F!Var U) : Var U. # (by DomRst,InSub).
    (G!Var T) : Var T and (G!Var V) : Var V. # (by DomRst,InSub).

[none]
    If S -| (F!Var S) and U -| (F!Var U) and J(F, G)
        then L(F!Var S, G!Var T) and M(F!Var U, G!Var V).

    Per V !! Mod T. Per T !! Mod V.
    Per S !! Mod U. Per U !! Mod S.

    For every I : Var (T||V) and every H : Var (S||U)
        if  S -| (F!Var S) and U -| (F!Var U) and J(F, G) and
            T :: (G ! Var T) -> (I ! Var T) and
            V :: (G ! Var V) -> (I ! Var V) and
            S :: (F ! Var S) -> (H ! Var S) and
            U :: (F ! Var U) -> (H ! Var U) and
            L(H!Var S, I!Var T) and M(H!Var U, I!Var V)
        then J(H,I).
[full]

    Then S -| (F!Var S) and U -| (F!Var U) (by PCTerm).
    Hence L(F!Var S, G!Var T) and M(F!Var U, G!Var V).

    Then (T||V) -| G (by PCTerm).

    Let I : Var (T||V) and (T||V) :: G -> I.
    Then there exists H : Var (S||U) such that (S||U) :: F -> H and J(H,I).
    proof.
        (I!Var T) : Var T and (I!Var V) : Var V (by DomRst).

        T :: (G ! Var T) >> (I ! Var T)
            and V :: (G ! Var V) >> (I ! Var V)
            and G,I coincide on Per (T||V) (by PCMove).

        T :: (G ! Var T) -> (I ! Var T). # (by DefMove).
        proof.
            Per T <= Var T. # (by DefVar).
            Per T <= Var (T||V). # (by TranSub).
            Per T !! Mod (T||V) (by DjUn,ModPer,PCMod).
            Per T <= Per (T||V) (by PerVar,DjCm).
            G,I coincide on Per T (by RstRst). # (by DefVar).
            (G ! Var T), (I ! Var T) coincide on Per T (by RstRst).
        end.

        V :: (G ! Var V) -> (I ! Var V). # (by DefMove).
        proof.
            Per V <= Var V. # (by DefVar).
            Per V <= Var (T||V). # (by TranSub).
            Per V !! Mod (T||V) (by DjUn,ModPer,PCMod).
            Per V <= Per (T||V) (by PerVar,DjCm).
            G,I coincide on Per V (by RstRst). # (by DefVar).
            (G ! Var V), (I ! Var V) coincide on Per V (by RstRst).
        end.

        Choose (P : Var S) such that
            S :: (F ! Var S) -> P and L(P,I!Var T) (by _). # (by DefRefF).
        Choose (Q : Var U) such that
            U :: (F ! Var U) -> Q and M(Q,I!Var V) (by _). # (by DefRefF).

        P,Q coincide on (Var S * Var U). # (by TranSub).
        proof.
            Var U = Mod U + Per U. # (by DefVar).
            Var S = Mod S + Per S. # (by DefVar).

            Mod S * Mod U = {} (by _).
            Mod S * Per U = {} (by CommIn).
            Mod S * Var U = {} (by DistLIn).
            Per S * Mod U = {} (by _).
            Per S * Var U = Per S * Per U (by DistLIn).
            Var S * Var U = Per S * Per U (by DistRIn).

            Per S <= Var S. # (by DefVar).
            (F ! Var S),P coincide on Per S. # (by DefMove).
            (F ! Var S),P coincide on Var S * Var U (by RstRst).
            F,P coincide on Var S * Var U (by RstRst,TranSub).

            Per U <= Var U. # (by DefVar).
            (F ! Var U),Q coincide on Per U. # (by DefMove).
            (F ! Var U),Q coincide on Var S * Var U (by RstRst).
            F,Q coincide on Var S * Var U (by RstRst,TranSub).
        end.

        Then P ++ Q : Var (S || U)
            and P ++ Q, P coincide on Var S
            and P ++ Q, Q coincide on Var U (by PCVar). # (by DefSum).

        (S||U) :: F -> P ++ Q (by PCMove).
        proof.
            P = ((P ++ Q) ! Var S) (by RstDom).
            S :: (F ! Var S) >> ((P ++ Q) ! Var S). # (by DefMove).

            Q = ((P ++ Q) ! Var U) (by RstDom).
            U :: (F ! Var U) >> ((P ++ Q) ! Var U). # (by DefMove).

            F, P++Q coincide on Per (S || U) (by CoinUn).
            proof.
                Per S <= Dom P and Per U <= Dom Q. # (by DefVar).
                Per S, Per U are subsets of Dom F. # (by TranSub).
                Var S, Var U are subsets of Dom (P ++ Q) (by PCVar).
                Per S, Per U are subsets of Dom (P ++ Q). # (by TranSub).

                F, P coincide on Per S (by RstRst). # (by DefMove, RstRst).
                P++Q, P coincide on Per S (by RstRst).

                F, Q coincide on Per U (by RstRst). # (by DefMove, RstRst).
                P++Q, Q coincide on Per U (by RstRst).

                Var (S || U) = (Mod S + Per S) + (Mod U + Per U) (by PCVar). # (by DefVar).
                Var (S || U) = (Mod S + Mod U) + (Per S + Per U) (by AssoUn,CommUn).
                Per (S || U) = (Per S + Per U) - (Mod S + Mod U) (by UnCm,PerVar,PCMod).
                (Per S + Per U) !! (Mod S + Mod U) (by DjUn,ModPer,CommIn).
                Per (S || U) = (Per S + Per U) (by DuCm).
            end.
        end.

        J(P ++ Q, I) (by RstDom).
    end.
qed.

[the seqcomp of s and t] [s ; t @ the seqcomp of s and t]

Axiom _SCWF.
    For all substitutions S,T  (S ; T) is a substitution.

Axiom SCVar.
    For all substitutions S,T  Var (S ; T) = Var S + Var T.

Axiom SCTerm.   Let S,T be substitutions and F : Var (S;T).
    (S ; T) -| F  <=>  S -| (F ! Var S) /\
            forall (H : Var (S;T)):
                S :: F ->> H  =>  T -| (H ! Var T).

Axiom SCMove.  Let S,T be substitutions and F,G : Var (S;T).
    (S ; T) :: F -> G  <=>  S -| (F ! Var S) =>
            exists (H : Var (S;T)):
                S :: F ->> H  /\  T :: H ->> G.


Theorem ReusePSC.
    Let S,T,U,V be substitutions and L,M,J be invariants.
    Assume S,U are compatible. Assume S [L= T and U [M= V.
    Then (S||U) [J= (T;V). # (by DefRefB).
Proof.
    (S||U) is a substitution.
    Let F : Var (S||U) and G : Var (T;V).
    Assume (S||U) -| F and J(F, G).

    Var S <= Dom F and Var U <= Dom F (by PCVar).
    Var T <= Dom G and Var V <= Dom G (by SCVar).
    (F!Var S) : Var S and (F!Var U) : Var U (by DomRst,InSub).
    (G!Var T) : Var T and (G!Var V) : Var V (by DomRst,InSub).

[none]
    If S -| (F!Var S) and U -| (F!Var U) and J(F, G) then L(F!Var S, G!Var T).
    If S -| (F!Var S) and U -| (F!Var U) and J(F, G) then
        for every (E : Var (T;V)) if T :: G ->> E then M(F!Var U, E!Var V).

    Per S !! Mod U. Per U !! Mod S.

    For every I,E : Var (T;V) and every H : Var (S||U)
        if  S -| (F!Var S) and U -| (F!Var U) and J(F, G) and
            T :: G ->> E and V :: E ->> I and
            S :: (F ! Var S) -> (H ! Var S) and
            U :: (F ! Var U) -> (H ! Var U) and
            L(H!Var S, E!Var T) and M(H!Var U, I!Var V)
        then J(H,I).
[full]

    Then S -| (F!Var S) and U -| (F!Var U) (by PCTerm).
    Then T -| (G!Var T). # (by DefRefF).

    Then (T;V) -| G (by SCTerm).
    proof.
        Let E : Var (T;V) and T :: G ->> E.
        (E!Var V) : Var V (by DomRst).
        Then V -| (E!Var V) (by _). # (by DefRefF).
[none]
    end. ## BAD, can't prove so far
[full]

    Let I : Var (T;V) and (T;V) :: G -> I.
    Then there exists H : Var (S||U) such that (S||U) :: F -> H and J(H,I).
    proof.
        (I!Var T) : Var T and (I!Var V) : Var V (by DomRst).

[none]
        Choose (E : Var (T;V)) such that
            T :: G ->> E and V :: E ->> I (by SCMove).
[full]  ## BAD

        (E!Var T) : Var T and (E!Var V) : Var V (by DomRst).

        T :: (G ! Var T) -> (E ! Var T). # (by DefBMove).
        V :: (E ! Var V) -> (I ! Var V). # (by DefBMove).

        Choose (P : Var S) such that
            S :: (F ! Var S) -> P and L(P,E!Var T) (by _). # (by DefRefF).
        Choose (Q : Var U) such that
            U :: (F ! Var U) -> Q and M(Q,I!Var V) (by _). # (by DefRefF).

        P,Q coincide on (Var S * Var U). # (by TranSub).
        proof.
            Var U = Mod U + Per U. # (by DefVar).
            Var S = Mod S + Per S. # (by DefVar).

            Mod S * Mod U = {} (by _).
            Mod S * Per U = {} (by CommIn).
            Mod S * Var U = {} (by DistLIn).
            Per S * Mod U = {} (by _).
            Per S * Var U = Per S * Per U (by DistLIn).
            Var S * Var U = Per S * Per U (by DistRIn).

            Per S <= Var S. # (by DefVar).
            (F ! Var S),P coincide on Per S. # (by DefMove).
            (F ! Var S),P coincide on (Var S * Var U) (by RstRst).
            F,P coincide on (Var S * Var U) (by RstRst,TranSub).

            Per U <= Var U. # (by DefVar).
            (F ! Var U),Q coincide on Per U. # (by DefMove).
            (F ! Var U),Q coincide on (Var S * Var U) (by RstRst).
            F,Q coincide on (Var S * Var U) (by RstRst,TranSub).
        end.

        Then P ++ Q : Var (S || U)
            and P ++ Q, P coincide on Var S
            and P ++ Q, Q coincide on Var U (by PCVar). # , DefSum).

        (S||U) :: F -> P ++ Q (by PCMove).
        proof.
            P = ((P ++ Q) ! Var S) (by RstDom).
            S :: (F ! Var S) >> ((P ++ Q) ! Var S). # (by DefMove).

            Q = ((P ++ Q) ! Var U) (by RstDom).
            U :: (F ! Var U) >> ((P ++ Q) ! Var U). # (by DefMove).

            F, P++Q coincide on Per (S || U) (by CoinUn).
            proof.
                Per S <= Dom P and Per U <= Dom Q. # (by DefVar).
                Per S, Per U are subsets of Dom F. # (by TranSub).
                Var S, Var U are subsets of Dom (P ++ Q) (by PCVar).
                Per S, Per U are subsets of Dom (P ++ Q). # (by TranSub).

                F, P coincide on Per S (by RstRst). #(by DefMove, RstRst).
                P++Q, P coincide on Per S (by RstRst).

                F, Q coincide on Per U (by RstRst). #(by DefMove, RstRst).
                P++Q, Q coincide on Per U (by RstRst).

                Var (S || U) = (Mod S + Per S) + (Mod U + Per U) (by PCVar). #,DefVar).
                Var (S || U) = (Mod S + Mod U) + (Per S + Per U) (by AssoUn, CommUn).
                Per (S || U) = (Per S + Per U) - (Mod S + Mod U) (by UnCm,PerVar,PCMod).
                (Per S + Per U) !! (Mod S + Mod U) (by DjUn,ModPer,CommIn).
                Per (S || U) = (Per S + Per U) (by DuCm).
            end.
        end.

        J(P ++ Q, I) (by RstDom).
    end.
qed.
[quit]  ## STOPS HERE

Theorem ReuseSC.
    Let S,T,U,V be substitutions and L,M,J be invariants.
    Assume S [L= T and U [M= V.
    Then (S;U) [J= (T;V) (by DefRefB).
Proof.
    Let F : Var (S;U) and G : Var (T;V).
    Assume (S;U) -| F and J(F, G).

    Var S <= Dom F and Var U <= Dom F (by SCVar).
    Var T <= Dom G and Var V <= Dom G (by SCVar).
    (F!Var S) : Var S and (F!Var U) : Var U (by DomRst,InSub).
    (G!Var T) : Var T and (G!Var V) : Var V (by DomRst,InSub).

[none]
    If S -| (F!Var S) and J(F, G) then L(F!Var S, G!Var T).

    If S -| (F!Var S) and J(F, G) then
        for every (D : Var(S;U)) and every (E : Var (T;V))
        if S :: F ->> D and T :: G ->> E and L(D!Var S, E!Var T)
            and U -| (D!Var U) then M(D!Var U, E!Var V).

    For every I,E : Var (T;V) and every H,D : Var (S;U)
        if  S -| (F!Var S) and J(F, G) and
            S :: F ->> D and U :: D ->> H and
            T :: G ->> E and V :: E ->> I and
            L(D!Var S, E!Var T) and M(H!Var U, I!Var V)
        then J(H,I).
[full]

    S -| (F!Var S) (by SCTerm).
    T -| (G!Var T) (by DefRefF).

    Then (T;V) -| G (by SCTerm).
    proof.
        Let E : Var (T;V) and T :: G ->> E.
        (E!Var V) : Var V and (E!Var T) : Var T (by DomRst).

        T :: (G!Var T) -> (E!Var T) (by DefBMove).

        Then take P : Var S such
            that S :: (F!Var S) -> P and L(P, E!Var T) (by DefRefF).

        (F-+P) : Var (S;U) (by DefOver,DomRst, CommIn).
        (F-+P) ! Var S = P (by DefOver,RstDom).
        (F-+P) ! Var U : Var U (by DomRst).
        (F-+P),F coincide on (Dom F - Dom P) (by DefOver).

        S :: F ->> (F-+P) (by DefBMove).

        Then U -| ((F-+P)!Var U) and M((F-+P)!Var U,E!Var V) (by SCTerm).
        Then V -| (E!Var V) (by DefRefF).
    end.

    Let I : Var (T;V) and (T;V) :: G -> I.
    Then there exists H : Var (S;U) such that (S;U) :: F -> H and J(H,I).
    proof.
        Choose (E : Var (T;V)) such that
            T :: G ->> E and V :: E ->> I (by SCMove).

        (I!Var T) : Var T and (I!Var V) : Var V (by DomRst).
        (E!Var T) : Var T and (E!Var V) : Var V (by DomRst).

        T :: (G ! Var T) -> (E ! Var T) (by DefBMove).

        Then take P : Var S such
            that S :: (F!Var S) -> P and L(P, E!Var T) (by DefRefF).

        (F-+P) : Var (S;U) (by DefOver,DomRst, CommIn).
        (F-+P) ! Var S = P (by DefOver,RstDom).
        (F-+P) ! Var U : Var U (by DomRst).
        (F-+P),F coincide on (Dom F - Dom P) (by DefOver).

        S :: F ->> (F-+P) (by DefBMove).

        Then U -| ((F-+P)!Var U) and M((F-+P)!Var U,E!Var V) (by SCTerm).

        V :: (E ! Var V) -> (I ! Var V) (by DefBMove).

        Then take (Q : Var U) such that
            U :: ((F-+P) ! Var U) -> Q and M(Q,I!Var V) (by DefRefF).

        ((F-+P)-+Q) : Var (S;U) (by DefOver,DomRst, CommIn).
        ((F-+P)-+Q) ! Var U = Q (by DefOver,RstDom).
        ((F-+P)-+Q),(F-+P) coincide on (Dom F - Dom Q) (by DefOver).

        U :: (F-+P) ->> ((F-+P)-+Q) (by DefBMove).

        (S;U) :: F -> ((F-+P)-+Q) (by SCMove).

        J((F-+P)-+Q, I) (by RstDom).
    end.
qed.
