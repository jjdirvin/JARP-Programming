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
datatype supported_type = integer | boolean | ERROR;


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

fun getIntValue (v) : int =
   case v of Bool(v) => raise Fail("getIntValue: Not int value")
           | Int(v) => v;
 
fun getBoolValue (v) : bool =
   case v of Bool(v) => v
           | Int(v) => raise Fail("getBoolValue: Not boolean value");

fun updateEnv(id, userType:supported_type, m as (e:env, a:addr, s:store)) = 
    let
        val newAddr = a+1;
        val newEnv = (id, userType, a)::e;
    in
        (newEnv, newAddr, s)
    end;

fun getUpdatedStore(loc:addr, dv:denotable_value, []) = (loc, dv)::[]
    | getUpdatedStore(loc, dv, S as v::vs) = 
        if(loc= #1 v) then (loc, dv)::vs
        else v::getUpdatedStore(loc, dv, vs);

fun updateStore(loc:addr, dv:denotable_value, m as (e:env, a:addr, s:store)) = 
        let
            val newS = getUpdatedStore(loc, dv, s)
        in
            (e, a, newS)
        end;

(*define printModel here too*)
(*Ideas: input is a triple: (environment, address, store)*)
(*output: to print out the environment, store, and addresses in a readable format*)


(* =========================================================================================================== *)
end; (* struct *) 
(* =========================================================================================================== *)











