;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                  PROJECT 2
;;                           LL(1) Parser for Scheme
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Requires R5RS to run

;; Loads the given utility functions in utilFuncs.ss
(load "utilFuncs.ss")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 1: Utility functions

;; getStartSymbol returns the start nonterminal of the grammar
;; As defined in the project description, the start nonterminal is the left-hand side nonterminal of the first rule of the grammar.
;; (This function is useful for generating initial FOLLOW sets)
;; Input: grammar
;; Output: the start non-terminal of the grammar.
(define getStartSymbol
  (lambda (grammar)
    (car(car grammar))
  ))

;; Returns a list of all nonterminals in the grammar
;; You may assume that every nonterminal in the grammar will have a rule.
;; input: the grammar
;; Output: the list of all nonterminals in the grammar: '(NT1 NT2 ... NTk)
(define getNonterminals
  (lambda (grammar)
    (if (null? grammar)
        grammar
        (cons (car (car grammar))(getNonterminals (cdr grammar))))
  ))

;; Returns a list of all production rules in the grammar.
;; If a rule happens to look like lhs ::= rhs1 | rhs2, getProductions will separate those two rules into different elements of the list
;; Input: the grammar
;; Output: the list of all production rules in the grammar
;; Output format example:
;;    Given an example grammar:
;;          NT1 ::= rhs1 | rhs2
;;          NT2 ::= rhs3
;;    Which is of the form
;;          '((NT1 (rhs1) (rhs2)) (NT2 (rhs3)))
;;    getProductions should return '((NT1 rhs1) (NT1 rhs2) (NT2 rhs3))
(define getProductions
  (lambda (grammar)
    (if (null? grammar)
        '()
        (if (= 1 (length (car grammar)))
            (getProductions(cdr grammar))
            (cons (cons (car(car grammar)) (cons (car(cdr(car grammar))) '())) (getProductions (cons (removeMatch (car grammar) (car(cdr(car grammar)))) (cdr grammar))))))
  ))

;; An associative list assocList is a list of pairs of the form '((a List_a) (b List_b) ... (k List_k)).
;;    Each pair has the form '(symbol list), where, for example, list can be the symbol's FIRST set or FOLLOW set.
;; updateAssocList updates the associative list by union-ing set with List_s given symbol s and returns the modified assocList
;;    If (s List_s) is not in assocList, just return assocList
;; Inputs:
;;    assocList: the associative list, a list of pairs of the form '((a List_a) (b List_b) ... (k List_k)).
;;    symbol: the symbol whose list, List(symbol), will be union-ed with set
;;    set: the set to be union-ed to the corresponding symbol
;; Output: the new assocList where the corresponding list for the symbol, is now List(symbol) U set.
;; Output format example:
;;    Given the following associative list assocListEx = '((a (2 3 4)) (b (4 5)))
;;    (updateAssocList assocListEx a '(4 5)) should return '((a (2 3 4 5)) (b (4 5)))
(define updateAssocList
  (lambda (assocList symbol set)
    (if (eq? (car (car assocList)) symbol)
        (cons (cons (car (car assocList)) (cons (union (car (cdr (car assocList))) set) '())) (cdr assocList))
        (cons (car assocList) (updateAssocList (cdr assocList) symbol set)))
  ))

;; Depending on the setting (either 'first or 'follow), getInitSets returns the initialized FIRST sets or FOLLOW sets for all non-terminals in the grammar
;; Inputs:
;;    NTS: the list of all nonterminals in the grammar
;;    startSymbol: the start nonterminal of the grammar
;;    setting: either 'first or 'follow
;; Output: Depending on what the setting is, initSets returns an initialized list of empty FIRST sets or FOLLOW sets for each nonterminal of the grammar
;; Output format example:
;;    Given an example grammar:
;;          NT1 ::= rhs1 | rhs2
;;          NT2 ::= rhs3
;;    Which is of the form
;;          '((NT1 (rhs1) (rhs2)) (NT2 (rhs3)))
;;    (getInitSets '(NT1 NT2) NT1 'first) returns '((NT1 ()) (NT2 ()))
;;    (getInitSets '(NT1 NT2) NT1 'follow) returns '((NT1 (eof)) (NT2 ()))
(define getInitSets
  (lambda (NTs startSymbol setting)
    (if (eq? setting 'first)
        (if (null? NTs)
            '()
            (cons (cons (car NTs) (cons '()'())) (getInitSets (cdr NTs) startSymbol setting)))
        (if (null? NTs)
            '()
            (if (eq? startSymbol (car NTs))
                (cons (cons (car NTs) (cons (cons 'eof '()) '())) (getInitSets (cdr NTs) startSymbol setting))
                (cons (cons (car NTs) (cons '()'())) (getInitSets (cdr NTs) startSymbol setting))))
        )
  ))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 2: Generating FIRST sets

;; genFirstFunc returns a function that computes FIRST(symbolSeq) given a sequence of symbols (terminals and nonterminals) and an initial list of FIRST sets for all nonterminals in the grammar.
;; Input:
;;    NTs: the list of all nonterminals in the grammar
;; Output:
;;    a function first that takes as input a sequence of symbols symbolSeq, and an initial list of FIRST sets firstSets, and outputs FIRST(symbolSeq)
;;        Input:
;;            symbolSeq: sequence of symbols
;;            firstSets: a list of (potentially unfinished) FIRST sets for all nonterminals in the grammar
;;        Output:
;;            FIRST(SymbolSeq): (first symbolSeq firstSets)
(define genFirstFunc
  (lambda (NTs)
    (letrec ((first
              (lambda (symbolSeq firstSets)
                (if (null? symbolSeq)
                    '()
                    (if (contains? NTs (car symbolSeq))
                        (if (contains? (cadr (assoc (car symbolSeq) firstSets)) (epsilon))
                            (if (null? (cdr symbolSeq))
                                (union (cadr (assoc (car symbolSeq) firstSets)) (first (cdr symbolSeq) firstSets))
                                (union (removeMatch (cadr (assoc (first (car symbolSeq) firstSets))) (epsilon)) (car (first (cdr symbolSeq) firstSets))))
                            (cadr (assoc (car symbolSeq) firstSets)))
                        (list (car symbolSeq))))
              )))
      first)))

;; recurseFirstSets goes through each rule in the grammar and updates the FIRST sets based on the current rule
;; Inputs:
;;     rules: the list of all production rules in the grammar
;;     firstSets: a list of (potentially unfinished) FIRST sets
;;     firstFunc: a function that takes as input a sequence of symbols and list of FIRST sets, and returns FIRST(sequence of symbols).
;;        You will pass firstFunc as a function. (This should be written in genFirstFunc)
;; Output: an updated firstSets after making one pass through all the rules in the grammar
(define recurseFirstSets
  (lambda (rules firstSets firstFunc)
    (if (null? rules)
        firstSets
        (let ((rhsRule (cadar rules))
              (lhsRule (caar rules)))
              (recurseFirstSets (cdr rules) (updateAssocList firstSets lhsRule (union (cadr (assoc lhsRule firstSets)) (firstFunc rhsRule firstSets))) firstFunc)
        ))
    ))

;; getFirstSets returns the FIRST sets of all nonterminals in the grammar if the FIRST sets had no change
;; Inputs:
;;     rules: the list of all production rules in the grammar
;;     firstSets: a list of (potentially unfinished) FIRST sets
;;     firstFunc: a function that takes as input a sequence of symbols and list of FIRST sets, and returns FIRST(sequence of symbols).
;; Output: the updated firstSets, which is a list of the FIRST sets of every non-terminal in the grammar
(define getFirstSets
  (lambda (rules firstSets firstFunc)
      (let ((newFirstSets (recurseFirstSets rules firstSets firstFunc)))
        (if (equal? firstSets newFirstSets) ;;If the FIRST sets have no change
            firstSets ;; then return the FIRST sets
            (getFirstSets rules newFirstSets firstFunc))))) ;; Otherwise, use the new FIRST sets and recurse

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 3: Generating FOLLOW sets

;; genFollowFunc returns a function that computes FOLLOW(symbolSeq) given a sequence of symbols (terminals and nonterminals) and an initial list of FOLLOW sets for all nonterminals in the grammar.
;; Input:
;;    NTs: the list of all nonterminals in the grammar
;; Output:
;;    a function follow that takes as input a sequence of symbols symbolSeq, and an initial list of FOLLOW sets, the variable trailer, and the list of COMPLETED FIRST sets firstSets, and outputs FOLLOW(symbolSeq)
;;        Input:
;;            symbolSeq: sequence of symbols
;;            followSets: a list of (potentially unfinished) FOLLOW sets for all nonterminals in the grammar
;;            trailer: trailer variable (Check the algorithm on FOLLOW sets)
;;            firstSets: list of COMPLETED FIRST sets for all nonterminals in the grammar
;;        Output:
;;            FOLLOW(symbolSeq): (follow symbolSeq followSets trailer firstSets)
(define genFollowFunc
  (lambda (NTs)
    (letrec ((follow
              (lambda (symbolSeq followSets trailer firstSets)
                (if (null? (cdr symbolSeq))
                    (if (contains? NTs (car symbolSeq))
                       (updateAssocList followSets (car symbolSeq) (union  (car (cdr (assoc (car symbolSeq) followSets))) trailer))
                        followSets)
                    (if (contains? NTs (car symbolSeq))
                        (let ((newFollow (updateAssocList followSets (car symbolSeq) (union  (car (cdr (assoc (car symbolSeq) followSets))) trailer))))
                        (if (contains? (cadr (assoc (car symbolSeq) firstSets)) (epsilon))
                            (follow (cdr symbolSeq) newFollow (union trailer (removeMatch (cadr (assoc (car symbolSeq) firstSets)) (epsilon))) firstSets)
                            (follow (cdr symbolSeq) newFollow (cadr (assoc (car symbolSeq) firstSets)) firstSets)
                            ))
                        (follow (cdr symbolSeq) followSets (list (car symbolSeq)) firstSets)
                        )
                )
                )
      ))follow)))

;; recurseFollowSets goes through each rule in the grammar and updates the FOLLOW sets based on the current rule
;; Inputs:
;;     rules: the list of all production rules in the grammar
;;     followSets: a list of (potentially unfinished) FOLLOW sets
;;     followFunc: a function that takes as input a sequence of symbols and list of FOLLOW sets, and returns FOLLOW(sequence of symbols).
;;        You will pass followFunc as a function. (This should be written in genFollowFunc)
;; Output: an updated followSets after making one pass through all the rules in the grammar
(define recurseFollowSets
  (lambda (rules followSets firstSets followFunc)
    (if (null? rules)
         followSets
        (let* ((rhsRule (reverse (cadar rules)))
               (lhsRule (caar rules))
               (trailer (cadr (assoc lhsRule followSets))))
          (recurseFollowSets (cdr rules) (followFunc rhsRule followSets trailer firstSets) firstSets followFunc)
        ))))

;; getFollowSets returns the FOLLOW sets of all nonterminals in the grammar if the FOLLOW sets had no change
;; Inputs:
;;     rules: the list of all production rules in the grammar
;;     followSets: a list of (potentially unfinished) FOLLOW sets
;;     followFunc: a function that takes as input a sequence of symbols and list of FOLLOW sets, and returns FOLLOW(sequence of symbols).
;; Output: the updated followSets, which is a list of the FOLLOW sets of every non-terminal in the grammar
(define getFollowSets
  (lambda (rules followSets firstSets followFunc)
    (let ((newFollowSets (recurseFollowSets rules followSets firstSets followFunc)))
      (if (equal? followSets newFollowSets)
          followSets
          (getFollowSets rules newFollowSets firstSets followFunc))
  )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;Section 4: Generating PREDICT sets

;; Generates the PREDICT sets for each rule in the grammar
;; Inputs:
;;     rules: the list of all production rules of the grammar
;;     NTs: the list of all nonterminals in the grammar
;;     firstSets: the FIRST sets of all nonterminals in the grammar
;;     followSets: the FOLLOW sets of all nonterminals in the grammar
;;     firstFunc: a function that takes as input a sequence of symbols and list of FIRST sets, and returns FIRST(sequence of symbols).
;; Output: a list of pairs, one for each production rule in the grammar, where the first element is the production rule output as a list, and the second element is the PREDICT set for that production rule
;; Output format example:
;;    Given an example grammar:
;;          A ::= xB | "eps"
;;          B ::= yA | "eps"
;;    Which is of the form
;;          â€™((A (x B) ()) (B (y A) ()))
;;    getPredictSets should return
;;          '(
;;            ((A ::= (x B)) (x))
;;            ((A ::= ("eps")) (eof))
;;            ((B ::= (y A)) (y))
;;            ((B ::= ("eps")) (eof)))
;; You MUST use let* for this problem:
;;    How do you define A? How do you define delta? How do you define FIRST(delta)?
(define getPredictSets
  (lambda (rules firstSets followSets firstFunc)
    (if (null? rules)
        '()
        (let* ((rhsRule (cadar rules))
               (lhsRule (caar rules))
               (first (firstFunc rhsRule firstSets))
                        (delta '::=))
        (if (contains? first (epsilon))
            (cons (cons (list lhsRule delta rhsRule) (cdr (assoc lhsRule followSets))) (getPredictSets (cdr rules) firstSets followSets firstFunc))
            (cons (cons (list lhsRule delta rhsRule) (cons (list first) '())) (getPredictSets (cdr rules) firstSets followSets firstFunc))
            )
             ))))
    

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Section 5: Tester functions

;; Example Grammars
(define grammar0 '((start (a))))
(define grammar1 '((a (x b) ("eps")) (b (y a) ("eps"))))
(define grammar2 '((start (expr)) (expr ("+" term term)) (term (a) (b) (c))))
(define grammar3 '((start (stmts))
                   (stmts (assgn morestmts))
                   (morestmts ("," stmts) ("eps"))
                   (assgn (var "=" value))
                   (var (a) (b) (c) (d) (e))
                   (value (0) (1) (2) (3) (4) (5) (6) (7) (8) (9))))

;; For the following commands, remember to comment them out using ";" before handing in the assignment.
;;    Your proj2.ss file should NOT output anything. These commands are only used to help you test your functions

;; Testing the grammars
;; To test the example grammars, substitute "grammar0" in (define grammar grammar0) with the appropriate grammar<num>.
;; Comment out the appropriate commands to test each function individually.
(define grammar grammar1)
(define NTs (getNonterminals grammar))
(define rules (getProductions grammar))
;;(define ass (updateAssocList grammar 'a '(2 5)))
(define startSymbol (getstartSymbol grammar))
(define in (getInitSets NTs startSymbol 'first))
(define firstFunc (genFirstFunc NTs))
(define firstSets (getFirstSets rules (getInitSets NTs startSymbol 'first) firstFunc))
;(define rec (recurseFirstLists(rules firstSets firstFunc)))
(define followFunc (genFollowFunc NTs))
(define followSets (getFollowSets rules (getInitSets NTs startSymbol 'follow) firstSets followFunc))
(define predictSets (getPredictSets rules firstSets followSets firstFunc))
(display "First sets\n")
firstSets
(display "Follow sets\n")
followSets
(display "Predict sets\n")
predictSets