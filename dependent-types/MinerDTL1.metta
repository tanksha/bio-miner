!(import! &self ../../hyperon-pln/metta/synthesis/Synthesize.metta)
!(extend-py! ../utils/helper.py)
!(import! &succ succAxiom.metta)

(= (init-miner $db $ms $highsurp)
    (superpose ((add-atom &self (= (refdb) $db))
                (add-atom &self (= (ms) (fromNumber $ms)))
                (add-atom &self (= (highsurp) $highsurp))
                (get-universe-size $db))))

(= (get-universe-size $db)
    (add-atom &self
      (= (universe-size)
        (let $u (collapse (match $db $x 1)) (tuple-count $u)))))

;; iSurprisingness formula
(= (iSurprisingness $pattern)
    (case $pattern (
      ((candidate (, $p1 $p2) $cnt)
      (let* (($pp1 (prob (count $p1)))
          ($pp2 (prob (count $p2)))
          ($p1p2 (* $pp1 $pp2)) ;; probability estimate 
          ($p (prob $cnt))) ;; empirical
          (/ (max (- $p $p1p2) (- $p1p2 $p)) $p)))
      ((candidate (, $p1 $p2 $p3) $cnt)
      (let* (($pp1 (prob (count $p1)))
          ($pp2 (prob (count $p2)))
          ($pp3 (prob (count $p3)))
          ($pp1p2 (prob (count (, $p1 $p2))))
          ($pp1p3 (prob (count (, $p1 $p3))))
          ($pp2p3 (prob (count (, $p2 $p3))))
          ;; probability estimate
          ($maxP (max (* $pp1p2 $pp3) (max (* $pp1p3 $pp2) (max (* $pp2p3 $pp1) (* $pp1 (* $pp2 $pp3))))))
          ($minP (min (* $pp1p2 $pp3) (min (* $pp1p3 $pp2) (min (* $pp2p3 $pp1) (* $pp1 (* $pp2 $pp3))))))
          ($p (prob $cnt))) ;; empirical
          (/ (max (- $p $maxP) (- $minP $p)) $p)))
      ($_ 0))))

(= (isurp ($ptrn $cnt))
  (if (> (iSurprisingness (candidate $ptrn $cnt)) (highsurp)) true false))

(= (fromDeb $pattern $Xvar $Yvar)
      (case ((get-metatype $pattern) $pattern)
         (((Variable $_) $pattern)
          (($_ ($a (VarIdx Z) $b)) ($a $Xvar $b))
          (($_ ($a $b (VarIdx (S Z)))) ($a $b $Yvar))
          ($_ $pattern))))

(= (fromDebruijn $ptrn $Xvar $Yvar)
    (case $ptrn (
      ((, $p1 $p2) (, (fromDeb $p1 $Xvar $Yvar) (fromDeb $p2 $Xvar $Yvar)))
      ((, $p1 $p2 $p3) (, (fromDeb $p1 $Xvar $Yvar) (fromDeb $p2 $Xvar $Yvar) (fromDeb $p3 $Xvar $Yvar)))
      ($_ (fromDeb $ptrn $Xvar $Yvar)))))

(= (count $pattern)
    (let $result 
      (case (match &self (= (refdb) $db) $db)
          (($db (let $dptrn (fromDebruijn $pattern $Xvar $Yvar) (collapse (match $db $dptrn $dptrn))))
           (%void% ())))
      (fromNumber (tuple-count $result))))

(= (get-witness $x) (: (WitnessOf $x) $x))
(= (sourcedb) (match &self (= (refdb) $db) (match $db $x (axiom $x))))
(= (succ-axiom) (match &succ $x $x))

(: kb (-> Atom))
(= (kb) (superpose ((get-witness (sourcedb))
                    (succ-axiom)
                    (: trueaxiom (true))
                    )))

;; Specialization Rule
(= (specialize-ruleX)
  (: specilizeX
    (-> (true)
        (axiom ($link $x $y))
        (specializationOf ($link (VarIdx Z) $y) ($link (VarIdx Z) (VarIdx (S Z)))))))

(= (specialize-ruleY)
  (: specilizeY
    (-> (true)
        (axiom ($link $x $y))
        (specializationOf ($link $x (VarIdx (S Z))) ($link (VarIdx Z) (VarIdx (S Z)))))))

;; support rule
(= (support-rule)
  (: support
    (-> (true)
        (specializationOf $sptrn $aptrn)
        (supportOf $sptrn (count $sptrn)))))

;; Minimum support rule
(= (minsupport-rule)
  (: minsupport 
    (-> (supportOf $ptrn $cnt)
        (⍃ $ms $cnt)
        (minsup $ptrn $ms))))

;; Conjunction rule
(= (support-cnj-rule)
  (: support-cnj
    (-> (minsup $ptrn1 $m)
        (minsup $ptrn2 $m)
        (supportOf (, $ptrn1 $ptrn1) (count (, $ptrn1 $ptrn1))))))

;; Minimum support transitivity rule
(: ms-transitivity-rule (-> Atom))
(= (ms-transitivity-rule)
    (: ms-transitivity
      (-> (minsup $sptrn $m)
          (specializationOf $sptrn $aptrn)
          (minsup $aptrn $m))))

;; iSurprisingness rule
(: surprisingness-rule (-> Atom))
(= (surprisingness-rule) 
    (: surprisingness 
      (-> (minsup $ptrn $m)
          (supportOf $ptrn $cnt)
          (surp $ptrn (isurp ($ptrn $cnt))))))

(: rb (-> Atom))
(= (rb) (superpose ((specialize-ruleX)
                    (specialize-ruleY)
                    (support-rule)
                    (minsupport-rule)
                    (support-cnj-rule)
                    (ms-transitivity-rule)
                    (surprisingness-rule)
)))

(: -> (-> Atom Atom Atom Type))

;; Test
; !(import! &db ../data/sample2.metta)
!(bind! &db (new-space))
!(add-atom &db (Inheritance B A))
!(add-atom &db (Inheritance C A))
!(add-atom &db (Inheritance D E))
!(add-atom &db (Inheritance C E))

!(init-miner &db 1 0.9)

; !(let* (($ms (ms))
;         ((: $proof (minsup $p $ms)) (synthesize (: $proof $something) kb rb (fromNumber 5))))
;       (minsup (fromDebruijn $p $Xvar $Yvar) $ms))

; real    7m31.837s
; user    7m30.878s
; sys     0m0.479s
; [(minsup (Inheritance $Xvar A) (S Z)), (minsup (Inheritance $Xvar E) (S Z)), (minsup (Inheritance $Xvar E) (S Z)), (minsup (Inheritance $Xvar A) (S Z)), (minsup (Inheritance C $Yvar) (S Z)), (minsup (Inheritance C $Yvar) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar E) (Inheritance $Xvar E)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance $Xvar A) (Inheritance $Xvar A)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (, (Inheritance C $Yvar) (Inheritance C $Yvar)) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z)), (minsup (Inheritance $Xvar (VarIdx (S Z))) (S Z))]

; !(let* (($ms (ms))
;         ((: $proof (surp $p $tf)) (synthesize (: $proof $something) kb rb (fromNumber 5))))
;       (surp $p $tf))

; [(surp (Inheritance (VarIdx Z) A) false), (surp (Inheritance (VarIdx Z) A) false), (surp (Inheritance (VarIdx Z) E) false), (surp (Inheritance (VarIdx Z) E) false), (surp (Inheritance (VarIdx Z) E) false), (surp (Inheritance (VarIdx Z) E) false), (surp (Inheritance (VarIdx Z) A) false), (surp (Inheritance (VarIdx Z) A) false), (surp (Inheritance C (VarIdx (S Z))) false), (surp (Inheritance C (VarIdx (S Z))) false), (surp (Inheritance C (VarIdx (S Z))) false), (surp (Inheritance C (VarIdx (S Z))) false)]
