[read refine/sets.ftl]
[read refine/prelim.ftl]

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
