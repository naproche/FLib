[read refine/sets.ftl]
[read refine/prelim.ftl]

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
