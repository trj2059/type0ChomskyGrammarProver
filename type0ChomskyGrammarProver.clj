;; MIT License
;;
;; Copyright (c) 2018 Anthony Johnson
;;
;;
;;Permission is hereby granted, free of charge, to any person obtaining a copy 
;;of this software and associated documentation files (the "Software"), to deal 
;;in the Software without restriction, including without limitation the rights to 
;;use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies 
;;of the Software, and to permit persons to whom the Software is furnished to 
;;do so, subject to the following conditions:
;;
;;The above copyright notice and this permission notice shall be included in all 
;;copies or substantial portions of the Software.
;;
;;THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR 
;;IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, 
;;FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE 
;;AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, 
;;WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN 
;;CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

;; a simple theorem prover for type 0 chomsky grammars.  executes a breadth first
;; search on infinite graphs

(defn union [s1 s2]
   (set (concat (seq s1) (seq s2)))
  )

(defn get-subst-lsts [cfg blk]
    (for [x (take
             (- (count cfg) (- blk 1))
             (iterate inc 1))]
      (concat
        (->> cfg (take (- x 1)))
        (conj
          (->> cfg
               (take-last (- (+ (count cfg) 1) (+ x blk)))
              )
          (seq
          (subvec
                (vec cfg)
                (- x 1)
                (+ x (- blk 1))
            ) ;;subvec
           ) ;;seq
         ) ;;conj
        ) ;;concat
     ) ;;for
   ) ;;defn

(defn apply-prods-of-len-n-to-cfg [cfg prods n]
    (for [j (remove
              (conj #{} cfg)
                (set
                  (for [x (get-subst-lsts cfg n)]
                    (flatten (replace prods x))
                   );;for
                );;set
             );;remove
         ]
        (cons j (cons cfg '()))
     );;for
  );;defn

(defn is-thm-proven [thm proof-set]
    (cond
        (= (first (first proof-set)) thm) true
        (= (first proof-set) nil) false
        :else (recur  thm (rest proof-set))
     );;cond
 );;defn

(defn apply-prods-of-len-n-to-proof-set [prods n proof-set]
  (let [prfs (for [k proof-set] (first k))]
   (for [k (reduce union
             (for [cfg prfs]
               (set
                  (apply-prods-of-len-n-to-cfg cfg prods n)
                );;set
               );;for
            );;reduce
          m proof-set
          :let [z (concat k (rest m))]
          :when (= (second k) (first m))]
         z
    );;for
   );;let
 );;defn


(defn apply-prods-to-proof-set [prods proof-set]
  (seq
   (reduce union
     (for
        [x prods]
          (apply-prods-of-len-n-to-proof-set (first x) (+ (.indexOf prods x) 1) proof-set)          
      );;for
    );;reduce
  );;seq
 );;defn

(defn get-proven-thm [thm proof-set]
   (cond
     (is-thm-proven thm proof-set)
      (loop [thm2 thm proof-set2 proof-set]
         (cond 
              (= (first (first proof-set2)) thm) (first proof-set2)
              (= (first proof-set2) nil) nil              
              :else (recur thm (rest proof-set2))
          );;cond         
       );;loop
      :else nil
    );;cond
 );;defn

(defn prove-thm [axioms thm depth dbg]
  (loop [proof-list '( ((S)) ) loop-depth depth]
    (do
     (if (= dbg true) (println proof-list))
     (cond
        (is-thm-proven thm proof-list) (get-proven-thm thm proof-list)
        (= 0 loop-depth) nil
        :else (recur (seq (union proof-list (apply-prods-to-proof-set axioms proof-list))) (- loop-depth 1))
       );;cond
     );;do      
   );;loop
 );;defn

(prove-thm [[{'(a) 'X, '(S) '(a b)}] [{'(a b) '(j x x)}] [{'(j x x) 'R}]] '(R) 10 false)
