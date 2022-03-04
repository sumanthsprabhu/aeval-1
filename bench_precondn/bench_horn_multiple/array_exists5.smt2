(declare-var a (Array Int Int))
(declare-var b (Array Int Int))
(declare-var a1 (Array Int Int))
(declare-var i Int)
(declare-var i1 Int)
(declare-var j1 Int)
(declare-var N Int)

(declare-rel inv ((Array Int Int) (Array Int Int) Int Int))
(declare-rel fail ())

(rule (=> (> N 0) (inv a ((as const (Array Int Int)) 1) 0 N)))

(rule (=> (and (inv a b i N) (< i N) (< 0 N)
    (= (store a i (select b i)) a1)
    (= i1 (+ i 1)))
  (inv a1 b i1 N)))

(rule (=> (and (inv a b i N) (>= i N)
  (not (exists ((j1 Int))
    (and (<= 0 j1) (< j1 N) (= (select a j1) 1))))) fail))

(query fail)
