[read ramsey/sets.ftl]
[read ramsey/numbers.ftl]
[read ramsey/utils.ftl]
[read ramsey/functions.ftl]

Let A,B,C,D,P,Q,R,S,T denote sets.
Let x,y,z denote elements.
Let i,j,k,l,m,n denote natural numbers.
Let F,G denote functions.

#
# Infinite Ramsey Theorem
#

Let a predecessor of i stand for
    a natural number j such that succ j = i.

Theorem RamseyInf.
    Let T be a finite set.
    For every (K << NAT)
        and every countable (S [= NAT)
        and every (c : [S/K] -> T)
    there exists
        an element u of T
        and a countable X [= S such that
    for every (Q << [X/K])
        c(Q) = u.

Proof by induction.

    Let K be a natural number.
    Let S be a countable subset of NAT.
    Let c : [S/K] -> T.

    Case K = 0.
        {} belongs to [S/0].
        For all (Q << [S/0]) c(Q) = c({}).
    end.

    Case K != 0.
        Take a predecessor k of K.

[prove off]
        Choose (N : NAT) such that N(0) = S and
            for all (i << NAT) if N(i) is a countable subset of NAT
                then N(succ i) is a countable subset of cdr N(i).
[/prove]

        We can prove by induction that for all (i << NAT)
                                N(i) is a countable subset of NAT.
            Indeed if i is nonzero then i has a predecessor
                                    and we have the thesis.

        We can prove by induction that for all (i,j << NAT)
                                    if j <= i then N(i) [= N(j).
            Indeed if j <= i and i has a predecessor
                                    then we have the thesis.

        For all nonequal (i,j << NAT) min N(i) != min N(j).
        proof.
            If i != j then succ j <= i or succ i <= j.
            If succ n <= m then N(m) [= cdr N(n) and min N(m) != min N(n).
        end.

        For all (i << NAT) and every set Q in [cdr N(i) / k]
            Q + min N(i) belongs to [S/K].
        proof.
            Let Q << [cdr N(i) / k].
            |Q + min N(i)| = K.
            Q + min N(i) [= S.
                Indeed N(i) [= S.
        end.

[prove off]
        Choose (C : NAT) such that for all (i << NAT)
            C(i) is a function from [cdr N(i) / k] such that
                 for every set Q in [cdr N(i) / k]
                        C(i)(Q) = c(Q + min N(i)).
[/prove]

        For every (i << NAT) Ran C(i) [= T.
        proof.
            Let x << Ran C(i).
            Take Q << [cdr N(i) / k] such that C(i)(Q) = x.
            x = c(Q + min N(i)) << Ran c.
        end.

        For every (i << NAT) and every countable X [= cdr N(i)
            every set Q in [X / k] belongs to [cdr N(i) / k].

        For every (i << NAT) there exists (u << T)
            and a countable subset X of cdr N(i) such that
                for every set Q in [X / k]
                    C(i)(Q) = u.
        proof.
            k -<- K.
            Take Y = cdr N(i) and d = C(i).
            Y is a countable subset of NAT and d : [Y / k] -> T.
            Take (u << T) and a countable subset X of Y such that
                for every set Q in [X / k] d(Q) = u (by _).
        end.

[prove off]
        For every (i << NAT) there exists (u << T) such that
                for every set Q in [N(succ i)/k]  C(i)(Q) = u.

        Choose (e : NAT) such that for every (i << NAT)
            e(i) = min N(i).

        Choose (d : NAT) such that for every (i << NAT)
            and every set Q in [N(succ i)/k]
                d(i) = C(i)(Q).
[/prove]
#
# And here the proof of the theorem begins
#
        Let us show that Ran d [= T.
            Ran d is a set. Let x << Ran d.
            Take (i << NAT) such that d(i) = x.
            Take nonempty X = [N(succ i)/k].
        end.

        Then Dir d << T and d[Dir d] is countable.
            Indeed d[Dir d] is nonempty.

        Take a set O equal to e{d[Dir d]}.

        O is a countable set (by ImgCount).
            Indeed d[Dir d] is a countable subset of NAT.

        For any element x of O there exists
            a natural number y such that y << d[Dir d] and e(y) = x.

        Let us prove that O [= S.
            Let x belong to O.
            Take (i << NAT) such that e(i) = x.
            N(i) [= S. Then x << S (by _).
        end.

        Let Q << [O/K].

        Q is a nonempty subset of O.
        Q is a subset of NAT.
        Q << Dom c.

        Let us show that c(Q) = Dir d.

            Take p = min Q.
            Take a set P equal to cdr Q.

            p belongs to Q. p belongs to O.
            P is a subset of Q. P is a subset of O.

            |P| = k.
                Indeed |Q| = succ k and succ |P| = |Q| and |P| << NAT.

            Then P belongs to [O/k].

            Choose (n << d[Dir d]) such that n << NAT and e(n) = p.
            d(n) = Dir d.

            P [= N(succ n).
            proof.
                Let x belong to P.
                Then x is a natural number in O.
                Choose a natural number m such that x = e(m).
                x = min N(m). Show by case analysis that x << N(succ n).
                Case N(m) [= N(succ n). Obvious.
                Case N(n) [= N(m).
                    p << N(m) and x << Q.
                    Then p = x (by MinMin).
                        Indeed Q and N(m) are nonempty subsets of NAT.
                    Hence p << P and we have a contradiction.
                end. end.
            end.

            Then c(Q) = d(n) (by ConsDiff).
            proof.
                Take D = cdr N(n). P << [D / k].
                Then c(P + min N(n)) = C(n)(P) (by _).
            end.
        end.
    end.
qed.
