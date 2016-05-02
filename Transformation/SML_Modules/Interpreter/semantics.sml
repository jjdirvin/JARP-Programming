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

fun E( itree(inode("Expression",_),
                [
                    Expression,
                    itree(inode("or",_), []),
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
                    period
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
                    itree(inode(variable,_), [])
                ]
            ),
        m
    ) = 
        let
            val m1 = updateEnv(variable, integer, m)
        in
            m1
        end
        
  | M( itree(inode("Declaration",_),
                [
                    itree(inode("bool",_), []),
                    itree(inode(variable,_), [])
                ]
            ),
        m
    ) = 
        let
            val m1 = updateEnv(variable, boolean, m)
        in
            m1
        end
       
  | M(  itree(inode(x_root,_), children),_) = raise General.Fail("\n\nIn M root = " ^ x_root ^ "\n\n")
  
  | M _ = raise Fail("error in Semantics.M - this should never occur")
  
fun FL(expr, assignment, block, m) = 
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

(* =========================================================================================================== *)
end (* struct *)
(* =========================================================================================================== *)








