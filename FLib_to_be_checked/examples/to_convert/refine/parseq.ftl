[read refine/sets.ftl]
[read refine/prelim.ftl]
[read refine/parcomp.ftl]
[read refine/seqcomp.ftl]

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
