(* =========================================================================================================== *)
structure Semantics =
struct


(* This makes contents of the Model structure directly accessible (i.e., the prefix "Model." is not needed. *)            
open Model; 
            
(* This makes the internal representation of parse trees directly accessible. *)            
open CONCRETE_REPRESENTATION;

(* The following tree structure, defined in the CONCERETE_REPRESENTATION structure, is used in the TL System:

    datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype INODE = inode of string * NODE_INFO
	                 | ...  
															
	datatype ITREE = itree of INODE * ITREE list;
*)


(* =========================================================================================================== *)
(* Here is where you add the M and E (as well as any other) definitions you developed in M2. The primary challenge here
   is to translate the parse expression notation we used in M2 to the actual SML tree patterns used in the TL System. 
   
   Example:
   
   M1: <stmtList> ::= <stmt> ";" <stmList>
   
   M2: M( [[ stmt_1 ; stmtList_1 ]], m) = M(stmtList_1, M(stmt_1,m))
    
   M4: 
        M( itree(inode("stmtList",_),
                    [
                        stmt,       (* this is a regular variable in SML and has no other special meaning *)
                        semiColon,  (* this is a regular variable in SML and has no other special meaning *)
                        stmtList    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        
        Note that the above M4 implementation will match ANY tree whose root is "stmtList" having three children.
        Such matches can be further constrained by explicitly exposing more of the tree structure.
        
        M( itree(inode("stmtList",_),
                    [
                        stmt,                       (* this is a regular variable in SML and has no other special meaning *)
                        itree(inode(";",_), [] ),   (* A semi-colon is a leaf node. All leaf nodes have an empty children list. *)
                        
                        stmtList                    (* this is a regular variable in SML and has no other special meaning *) 
                    ]
                ),
           m
           
        ) = M( stmtList, M(stmt, m) )  
        
        Note that the above M4 implementation will match ANY tree satisifying the following constraints:
            (1) the root is "stmtList"
            (2) the root has three children
            (3) the second child is a semi-colon   
*)

fun exponent(x, 0) = 1
    | exponent(x, y) = 
        if(y<0) then raise Fail("non-integer not supported: exponent")
        else x*exponent(x, y-1);

fun E( itree(inode("Expression",_),
                [
                    Expression,
                    itree(inode("or",_), [] ),
                    AndExpression
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(Expression, m)
            val (v2, m2) = E(AndExpression, m1)
            val v3 = getBoolValue(v1) orelse getBoolValue(v2)
        in
            (Bool(v3), m2)
        end
            
  | E( itree(inode("AndExpression",_),
                [
                    AndExpression,
                    itree(inode("and",_), []),
                    TerminalLogicExpression
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(AndExpression, m)
            val (v2, m2) = E(TerminalLogicExpression, m1)
            val v3 = getBoolValue(v1) andalso getBoolValue(v2)
        in
            (Bool(v3), m2)
        end
          
  | E( itree(inode("TerminalLogicExpression",_),
                [
                    itree(inode("not",_), []),
                    itree(inode("(",_), []),
                    Expression,
                    itree(inode(")",_), [])
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(Expression, m)
            val v2 = not(getBoolValue(v1))
        in
            (Bool(v2), m1)
        end
        
  | E( itree(inode("TerminalLogicExpression",_),
                [
                    itree(inode("true",_), [])
                ]
            ),
        m
    ) = (Bool(true), m)
  
  | E( itree(inode("TerminalLogicExpression",_),
                [
                    itree(inode("false",_), [])
                ]
            ),
        m
    ) = (Bool(false), m)
      
  | E( itree(inode("RelationalExpression",_),
                [
                    MathExpression,
                    itree(inode(">",_), []),
                    MathExpression1
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(MathExpression, m)
            val (v2, m2) = E(MathExpression1, m1)
            val v3 = (getIntValue(v1) > getIntValue(v2))
        in
            (Bool(v3), m2)
        end
        
  | E( itree(inode("RelationalExpression",_),
                [
                    MathExpression,
                    itree(inode("<",_), []),
                    MathExpression1
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(MathExpression, m)
            val (v2, m2) = E(MathExpression1, m1)
            val v3 = (getIntValue(v1) < getIntValue(v2))
        in
            (Bool(v3), m2)
        end
  | E( itree(inode("RelationalExpression",_),
                [
                    MathExpression,
                    itree(inode("=",_), []),
                    MathExpression1
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(MathExpression, m)
            val (v2, m2) = E(MathExpression1, m1)
            val v3 = (getIntValue(v1) = getIntValue(v2))
        in
            (Bool(v3), m2)
        end
  
  | E( itree(inode("RelationalExpression",_),
                [
                    MathExpression,
                    itree(inode("!=",_), []),
                    MathExpression1
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(MathExpression, m)
            val (v2, m2) = E(MathExpression1, m1)
            val v3 = not(getIntValue(v1) = getIntValue(v2))
        in
            (Bool(v3), m2)
        end
  
  | E( itree(inode("MathExpression",_),
                [
                    MathExpression,
                    itree(inode("+",_), []),
                    Term
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(MathExpression, m)
            val (v2, m2) = E(Term, m1)
            val v3 = getIntValue(v1) + getIntValue(v2)
        in
            (Int(v3), m2)
        end
        
  | E( itree(inode("MathExpression",_),
                [
                    MathExpression,
                    itree(inode("-",_), []),
                    Term
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(MathExpression, m)
            val (v2, m2) = E(Term, m1)
            val v3 = getIntValue(v1) - getIntValue(v2)
        in
            (Int(v3), m2)
        end
        
  | E( itree(inode("Term",_),
                [
                    Term,
                    itree(inode("mod",_), []),
                    Exponent
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(Term, m)
            val (v2, m2) = E(Exponent, m1)
        in
            if getIntValue(v2) = 0 then raise Fail("Divide by 0!")
            else 
                let
                    val v3 = (getIntValue(v1) mod getIntValue(v2))
                in
                    (Int(v3), m2)
                end
        end
        
  | E( itree(inode("Term",_),
                [
                    Term,
                    itree(inode("div",_), []),
                    Exponent
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(Term, m)
            val (v2, m2) = E(Exponent, m1)
        in
            if getIntValue(v2) = 0 then raise Fail("Divide by 0!")
            else 
                let
                    val v3 = (getIntValue(v1) div getIntValue(v2))
                in
                    (Int(v3), m2)
                end
        end
        
  | E( itree(inode("Term",_),
                [
                    Term,
                    itree(inode("*",_), []),
                    Exponent
                ]
            ),
        m
    ) =
        let
            val (v1, m1) = E(Term, m)
            val (v2, m2) = E(Exponent, m1)
            val v3 = (getIntValue(v1) * getIntValue(v2))
        in
            (Int(v3), m2)
        end
        
  | E( itree(inode("Exponent",_),
                [
                    UnaryM,
                    itree(inode("^",_), []),
                    Exponent
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(UnaryM, m)
            val (v2, m2) = E(Exponent, m1)
            val v3 = exponent(getIntValue(v1), getIntValue(v2))
        in
            (Int(v3), m2)
        end
        
  | E( itree(inode("UnaryM",_),
                [
                    itree(inode("-",_), []),
                    Factor
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(Factor, m)
            val v2 = ~1 * getIntValue(v1)
        in
            (Int(v2), m1)
        end
  
  | E( itree(inode("Factor",_),
                [
                    itree(inode("(",_), []),
                    Expression,
                    itree(inode(")",_), [])
                ]
            ),
        m
    ) = E(Expression, m)
    
  | E( itree(inode("Factor",_),
                [
                    itree(inode("|",_), []),
                    Expression,
                    itree(inode("|",_), [])
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(Expression, m)
        in
            if(getIntValue(v1)>0) then (v1, m1)
            else (Int(getIntValue(v1) * ~1), m1)
        end
   
  | E( itree(inode("Factor",_),
                [
                    itree(inode("variable",_), [x])
                ]
            ),
        m
    ) = 
        let
            val v1 = accessStore(getLoc(accessEnv(getLeaf(x), m)), m)
        in
            (v1, m)
        end

  | E( itree(inode("Factor",_),
                [
                    itree(inode("number",_), [x])
                ]
            ),
        m
    ) = 
        let
            val v1 = Int.fromString(getLeaf(x))
            val v2 = getOpt(v1, 0)
        in
            (Int(v2), m)
        end
        
  | E( itree(inode("PreIncDec",_),
                [
                    itree(inode("++",_), []),
                    itree(inode("variable",_), [x])
                ]
            ),
        m
    ) = 
        let
            val v1 = accessStore(getLoc(accessEnv(getLeaf(x), m)), m)
            val v2 = getIntValue(v1)+1
            val m2 = updateStore(getLoc(accessEnv(getLeaf(x), m)), Int(v2), m)
        in
            (Int(v2), m2)
        end
        
  | E( itree(inode("PreIncDec",_),
                [
                    itree(inode("--",_), []),
                    itree(inode("variable",_), [x])
                ]
            ),
        m
    ) = 
        let
            val v1 = accessStore(getLoc(accessEnv(getLeaf(x), m)), m)
            val v2 = getIntValue(v1)-1
            val m2 = updateStore(getLoc(accessEnv(getLeaf(x), m)), Int(v2), m)
        in
            (Int(v2), m2)
        end
        
  | E( itree(inode("PostIncDec",_),
                [
                    itree(inode("variable",_), [x]),
                    itree(inode("--",_), [])
                ]
            ),
        m
    ) = 
        let
            val v1 = accessStore(getLoc(accessEnv(getLeaf(x), m)), m)
            val v2 = getIntValue(v1)-1
            val m1 = updateStore(getLoc(accessEnv(getLeaf(x), m)), Int(v2), m)
        in
            (v1, m1)
        end
        
  | E( itree(inode("PostIncDec",_),
                [
                    itree(inode("variable",_), [x]),
                    itree(inode("++",_), [])
                ]
            ),
        m
    ) = 
        let
            val v1 = accessStore(getLoc(accessEnv(getLeaf(x), m)), m)
            val v2 = getIntValue(v1)+1
            val m1 = updateStore(getLoc(accessEnv(getLeaf(x), m)), Int(v2), m)
        in
            (v1, m1)
        end
        
  | E(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn E root = " ^ x_root ^ "\n\n")
  
  | E _ = raise Fail("error in Semantics.E - this should never occur")

fun M(  itree(inode("prog",_), 
                [ 
                    StatementList, 
                    period 
                ] 
             ), 
        m
    ) = m
    
  | M( itree(inode("StatementList",_), 
                [ 
                    Statement,
                    itree(inode(";",_), [] ), 
                    StatementList
                ] 
             ), 
        m
    ) = M(StatementList, M(Statement, m))
    
  |M( itree(inode("StatementList",_), 
                [ 
                    Epsilon
                ] 
             ), 
        m
    ) = M(Epsilon, m)
  
  | M( itree(inode("Epsilon",_),
                [
                ]
            ),
        m
    ) = m
    
  | M( itree(inode("Block", _),
                [
                    itree(inode("(",_), [] ),
                    StatementList,
                    itree(inode(")",_), [] )
                ]
            ),
        m
    ) =
        let
            val (env1, addr1, s1) = M(StatementList, m)
            val m1 = (#1 m, #2 m, s1)
        in
            m1
        end
        

  | M( itree(inode("Declaration",_),
                [
                    itree(inode("int",_), []),
                    itree(inode("variable",_), [x])
                ]
            ),
        m
    ) = 
        let
            val m1 = updateEnv(getLeaf(x), integer, m)
        in
            m1
        end
        
  | M( itree(inode("Declaration",_),
                [
                    itree(inode("bool",_), []),
                    itree(inode("variable",_), [x])
                ]
            ),
        m
    ) = 
        let
            val m1 = updateEnv(getLeaf(x), boolean, m)
        in
            m1
        end
   
  | M( itree(inode("Assignment",_),
                [
                    itree(inode("variable",_), [x]),
                    itree(inode(":=",_), []),
                    Expression
                ]
            ),
        m
    ) = 
        let
            val (v1, m1) = E(Expression, m)
            val m2 = updateStore(getLoc(accessEnv(getLeaf(x), m1)), v1, m1)
        in
            m1
        end

    | M( itree(inode("Forloop",_),
                [
                    itree(inode("for",_), []),
                    itree(inode("(",_), []),
                    Assignment1,
                    itree(inode(";",_), []),
                    Expression,
                    itree(inode(";",_), []),
                    Assignment2,
                    itree(inode(")",_), []),
                    Block
                ]
            ),
        m
    ) =
        let
          val m1 = M(Assignment1, m)
          val m2 = FL(Expression, Assignment2, Block, m1)
        in
          m1
        end
       
  | M( itree(inode("Whileloop",_),
                [
                    itree(inode("while",_), []),
                    itree(inode("(",_), []),
                    Expression,
                    itree(inode(")",_), []),
                    Block
                ]
            ),
        m
    ) = WL(Expression, Block, m)
   
  | M( itree(inode("PreIncDec",_),
                [
                    itree(inode("++",_), []),
                    itree(inode(variable,_), [x])
                ]
            ),
        m
    ) = 
        let
            val v1 = accessStore(getLoc(accessEnv(getLeaf(x), m)), m)
            val v2 = getIntValue(v1)+1
            val m2 = updateStore(getLoc(accessEnv(getLeaf(x), m)), Int(v2), m)
        in
            m2
        end
        
  | M( itree(inode("PreIncDec",_),
                [
                    itree(inode("--",_), []),
                    itree(inode(variable,_), [x])
                ]
            ),
        m
    ) = 
        let
            val v1 = accessStore(getLoc(accessEnv(getLeaf(x), m)), m)
            val v2 = getIntValue(v1)-1
            val m2 = updateStore(getLoc(accessEnv(getLeaf(x), m)), Int(v2), m)
        in
            m2
        end
        
  | M( itree(inode("PostIncDec",_),
                [
                    itree(inode(variable,_), [x]),
                    itree(inode("--",_), [])
                ]
            ),
        m
    ) = 
        let
            val v1 = accessStore(getLoc(accessEnv(getLeaf(x), m)), m)
            val v2 = getIntValue(v1)-1
            val m1 = updateStore(getLoc(accessEnv(getLeaf(x), m)), Int(v2), m)
        in
            m1
        end
        
  | M( itree(inode("PostIncDec",_),
                [
                    itree(inode(variable,_), [x]),
                    itree(inode("++",_), [])
                ]
            ),
        m
    ) = 
        let
            val v1 = accessStore(getLoc(accessEnv(getLeaf(x), m)), m)
            val v2 = getIntValue(v1)+1
            val m1 = updateStore(getLoc(accessEnv(getLeaf(x), m)), Int(v2), m)
        in
             m1
        end
       
  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")

and FL(expr, assignment, block, m) = 
    let
        val (v1, m1) = E(expr, m)
    in
        if getBoolValue(v1) then
            let
                val m2 = M(block, m1)
                val m3 = M(assignment, m2)
                val m4 = FL(expr, assignment, block, m3)
            in
                m4
            end
        else
            m1
    end
    
and WL(expr, block, m) =
  let
      val (v1, m1) = E(expr, m)
  in
      if getBoolValue(v1) then
          let
              val m2 = M(block, m1)
              val m3 = WL(expr, block, m2)
          in
            m3
          end
      else
          m1
  end

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








