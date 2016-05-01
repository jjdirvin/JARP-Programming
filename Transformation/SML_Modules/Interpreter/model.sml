(* =========================================================================================================== *)
structure Model =

struct 

(* =========================================================================================================== *)
(* This function may be useful to get the leaf node of a tree -- which is always a string (even for integers).
   It is up to the interpreter to translate values accordingly (e.g., string to integer and string to boolean).
   
   Consult (i.e., open Int and open Bool) the SML structures Int and Bool for functions that can help with 
   this translation. 
*)
fun getLeaf( term ) = CONCRETE.leavesToStringRaw term 


(* For your typeChecker you may want to have a datatype that defines the types 
  (i.e., integer, boolean and possibly error) in your language. *)
datatype supported_type = integer | boolean;


(* It is recommended that your model store integers and Booleans in an internal form (i.e., as terms belonging to
   a userdefined datatype (e.g., denotable_value). If this is done, the store can be modeled as a list of such values.
*)
datatype denotable_value = Int of int | Bool of bool;

type addr  = int
type env   = (string * supported_type * addr) list
type store = (addr * denotable_value) list


(* The model defined here is a triple consisting of an environment, an address counter, and a store. The environment
   and the store are lists similar to what we have used in class. The address counter serves as an implementation of
   new(). Note that, depending on your implementation, this counter either contains the address of (1) the
   next available memory location, or (2) the last used memory location -- it all depends on when the counter is 
   incremented. *)
val initialModel = ( []:env, 0:addr, []:store )

fun updateEnv(id, userType:supported_type, m as (e:env, a:addr, s:store)) = 
    let
        val newAddr = a+1;
        val newEnv = (id, userType, a)::e;
    in
        (newEnv, newAddr, s)
    end;
    
fun getLoc(loc:addr, t:supported_type) = loc;
fun getType(loc:addr, t:supported_type) = t;


  (* id * m --> (loc, type) *)
fun accessEnv(id, ([]:env, a:addr, s:store)) = raise Fail("Not found in env")
  | accessEnv(id, m as ((id2, t, loc)::e:env, a:addr, s:store)) =
      if id = id2 then (t, loc) else accessEnv(id, (e, a, s));
      
      
(* loc * store -> dv *)
fun accessStore(loc:addr, (e:env, a:addr, []:store)) = raise Fail("Not found in store")
  | accessStore(loc:addr, (e:env, a:addr, (loc2, dv)::s:store)) =
      if loc = loc2 then dv else accessStore(loc, (e, a, s));



(*define printModel here too*)
(*Ideas: input is a triple: (environment, address, store)*)
(*output: to print out the environment, store, and addresses in a readable format*)

fun getDVTypeAsString (t) : string = 
    case t of Bool(t) => "bool"
            | Int(t) => "int";
            
            
fun getSupportedTypeAsString (st) : string = 
    case st of integer => "integer"
            | boolean => "boolean";           
            
fun getIntValue (v) : int =
    case v of Bool(v) => raise Fail("getIntValue: Not int value")
            | Int(v) => v;
  
fun getBoolValue (v) : bool =
    case v of Bool(v) => v
            | Int(v) => raise Fail("getBoolValue: Not boolean value");
  
fun performAddition (q: denotable_value, r: denotable_value) : int = 
    if (getDVTypeAsString(q) = "int") andalso (getDVTypeAsString(r) = "int") then (getIntValue(q) + getIntValue(r))
    else ~1;


fun getEnvTripleAsString (s, st, a) : string = 
     ("( " ^s ^ ", " ^ (getSupportedTypeAsString(st)) ^ ", " ^ (Int.toString(a)) ^ " )\n");
    
fun getStrTupleAsString (a, dv) : string =
    if (getDVTypeAsString(dv) = "int") then ("( " ^ (Int.toString(a)) ^ ", " ^ (Int.toString(getIntValue(dv))) ^ " )\n")
    else ("( " ^ (Int.toString(a)) ^ ", " ^ (Bool.toString(getBoolValue(dv))) ^ " )\n");

fun printEnvList ( [] )    = print "No items left in Environment List\n\n"
  | printEnvList ( x::xs ) = (print (getEnvTripleAsString(x)); printEnvList(xs));
  
fun printStrList ( [] )    = print "No items left in Store List\n"
  | printStrList ( x::xs ) = (print (getStrTupleAsString(x)); printStrList(xs));
  
  
fun printModel( envList, counter, strList ) = ( (print "\n--- Environment List ---\n(variable name, type, addr)\n"; (printEnvList(envList))); 
                                                (print "--- Store List ---\n(addr, value)\n"; (printStrList(strList)));
                                                (print ("\nCurrent Address Counter: " ^ (Int.toString(counter)) ^ "\n\n--- End of Model ---")) );


(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)











