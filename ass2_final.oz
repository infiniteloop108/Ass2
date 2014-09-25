%=============================================================================================
%Starting SAS
%SAS is a dictionary which maps environment variables to a 2-element list.
%1st element of that list contains the parent (in the Disjoint Set Data Structure). 2nd elemet signifies whether it is bound or unbound
%To see the status of a variable you have to look at its root.

%=============================================================================================
%Declare dictionary for SAS

declare
SAS = {Dictionary.new}

%=============================================================================================
%Add a new value to SAS

declare
proc {SASAdd X}
   {Dictionary.put SAS X [X unBOUND]}
end

%=============================================================================================
%Function for getting parent node in equivalence class

declare
fun {RetrieveNodeSAS Var}
   local Node in
      Node={Dictionary.get SAS Var}
      if Node.1==Var then Node
      else
	 %Path Compression
	 {Dictionary.put SAS Var {RetrieveNodeSAS Node.1}}
	 {Dictionary.get SAS Var}
      end
   end
end

%=============================================================================================
%Function for getting value of a variable

declare
fun {GetValFromSAS Var}
   local Node in
      Node={RetrieveNodeSAS Var}
      %Second element of the list
      Node.2.1
   end
end

%=============================================================================================
%Function for getting the parent variable of a variable

declare
fun {GetParFromSAS Var}
   local Node in
      Node={RetrieveNodeSAS Var}
      %First element of the list
      Node.1
   end
end

%=============================================================================================
% Check if the entries in a *sorted* pair-list are unique.

declare
fun {HasUniqueEntries P}
   local HasUniqueEntriesAux in
      fun {HasUniqueEntriesAux L}
	 case L
	 of H|T then
	    case T
	    of nil then true
	    [] !H|T1 then false
	    else {HasUniqueEntriesAux T}
	    end
	 end
      end
      {HasUniqueEntriesAux {Map P fun {$ X} X.1 end}} 
   end
end

%=============================================================================================
% equals Value.'<' if A and B are of the same type.
% Otherwise, any number is treated less than any literal.

declare
fun {MixedCompare A B}
   local  C D in
      case A
      of literal(C)|P
      then
	 case B
	 of literal(D)|Q
	 then
	    if {IsNumber C}=={IsNumber D}
	    then C < D
	    else {IsNumber C} end
	 end
      end
   end
end

%=============================================================================================\
%Return Record Pairs with features in sorted order
% The list of fieldname#value pairs can be specified in any
% order. The function returns a list of pairs sorted in the "arity"
% order - numerical fieldnames first, sorted in ascending order, 
% followed by lexicographic fieldnames in alphabetical order.

declare
fun {SortRecordPairs Pairs}
   local SR in
      SR = {Sort Pairs MixedCompare}
      if {HasUniqueEntries SR} then SR
      else raise illegalRecord(Pairs) end
      end
   end
end

%=============================================================================================
%Check if records-pairs are compatible (Assumes that the record-pairs are already sorted)

declare
fun {RecPairsComp P1 P2}
   local RecPairsCompAux in
      fun {RecPairsCompAux Xs Ys SoFar}
	 case Xs
	 of nil then
	    case Ys
	    of nil then SoFar
	    else false
	    end
	 [] X|Xr then
	    case Ys
	    of nil then false
	    [] Y|Yr then
	       case X.1#Y.1
	       of literal(A)#literal(B) then
		  if A == B then {RecPairsCompAux Xr Yr SoFar}
		  else {RecPairsCompAux Xr Yr false}
		  end
	       else
		  raise illegalRecord(Xs) end
	       end
	    end
	 end
      end
      {RecPairsCompAux P1 P2 true}
   end
end

%=============================================================================================
%Function to bind an unbound environment variable to a value.

declare
proc {ValBind X V}
   local NodeX SV in
      %SV is the sorted Value (if it is a record)
      case V
      of [record R P] then SV=[record R {SortRecordPairs P}]
      else SV=V
      end
      NodeX={RetrieveNodeSAS X}
      {Dictionary.put SAS NodeX.1 [NodeX.1 SV]}
   end
end

%=============================================================================================
%Function to bind unBOUND X to Y.

declare
proc {VarBind X Y}
   local NodeX  in
      NodeX={RetrieveNodeSAS X}
      {Dictionary.put SAS NodeX.1 [Y unBOUND]}
   end
end

%=============================================================================================
%Unifying two expressions. An expressions could be a variable (ident(X)) or a value (literal, record or proc)

declare
proc {UnifySAS Exp1 Exp2}
   local UnifySASAux in
      proc {UnifySASAux Exp1 Exp2 UnifSoFar}
	 %If we have already unified these expressions then skip
	 if {List.member [Exp1 Exp2] UnifSoFar} then skip
	 else
	    local NewUnif in
	       NewUnif = [Exp1 Exp2] | UnifSoFar
	       case Exp1
	       of ident(X) then
		  case Exp2
		  of ident(Y) then
		     %X and Y, both are variables
		     local Val1 Val2 in
			Val1 = {GetValFromSAS X}
			Val2 = {GetValFromSAS Y}
			if Val1 == unBOUND then
			   %X is unBound
			   {VarBind X Y}
			else
			   %X is Bound
			   if Val2 == unBOUND then {VarBind Y X}
			   else
			      %Y is also Bound
			      if {GetParFromSAS X} \= {GetParFromSAS Y} then {UnifySASAux Val1 Val2 NewUnif} end
			   end
			end
		     end
		  else
		     %X is a variable, Exp2 is a value
		     local Val1 in
			Val1 = {GetValFromSAS X}
			if Val1==unBOUND then {ValBind X Exp2}
			else {UnifySASAux Val1 Exp2 NewUnif}
			end
		     end
		  end
	       else
		  %Exp1 is a value
		  case Exp2
		  of ident(Y) then
		     %Y is a variable
		     local Val2 in
			Val2 = {GetValFromSAS Y}
			if Val2==unBOUND then {ValBind Y Exp1}
			else {UnifySASAux Exp1 Val2 NewUnif}
			end
		     end
		  else
		     %Exp1 and Exp2, both are values
		     case Exp1
		     of literal(X) then
			%Exp1 is a literal
			case Exp2
			of literal(Y) then
			   if X==Y then skip
			   else raise illass(Exp1 Exp2) end
			   end
			else raise typemis(Exp1 Exp2) end
			end
		     [] [record literal(R1) P1] then
			%Exp1 is a record
			case Exp2
			of [record literal(R2) P2] then
			   %Both the expressions are records. Check if they are compatible. If Yes, Merge. No, raise illegal assignment
			   local SP1 SP2 in
			      SP1 = {SortRecordPairs P1}
			      SP2 = {SortRecordPairs P2}
			      if R1 \= R2 then raise illass(Exp1 Exp2) end
			      else
				 if {RecPairsComp SP1 SP2} \= true then raise illass(Exp1 Exp2) end
				 else
				    {List.zip SP1 SP2 fun {$ A B} {UnifySASAux A.2.1 B.2.1 NewUnif} unit end _ }
				 end
			      end
			   end
			else raise typemis(Exp1 Exp2) end
			end
		     [] [procedure FP B RE] then
			%Exp1 is a procedure
			case Exp2
			of literal(Y) then raise typemis(Exp1 Exp2) end
			[] [record literal(R2) P2] then raise typemis(Exp1 Exp2) end
			[] [procedure FP2 B2 RE] then raise procmis(Exp1 Exp2) end
			end
		     end
		  end
	       end
	    end
	 end
      end
      {UnifySASAux Exp1 Exp2 nil}
   end
end

%SAS ends here

%=============================================================================================
%For generating environment variables

declare
TotVar={NewCell 0}

declare
fun {GetID}
   %Function to generate a unique Environment variable for an identifier.
   TotVar:=@TotVar+1
   @TotVar
end

%=============================================================================================
%Function to return the environment variable for the identifier.

declare
fun {EnvMap X Env}
   %If it is not yet defined, then raise an exception
   if {Dictionary.member Env X}==false then raise varndec(X) end
   else
      %Return the mapped environment variable
      {Dictionary.get Env X}
   end
end

%=============================================================================================
%Function to map an expression with identifiers with environment variables.

declare
fun {IdenMap V Env}
   case V
   of H|T then {IdenMap H Env}|{IdenMap T Env}
   [] ident(X) then ident({EnvMap X Env})
   else V
   end
end

%=============================================================================================
%Closure for procedures

%=============================================================================================
%Find list of free variables in the function's Actual Parameters list

declare
fun {AddArgList AP Env Bound Free}
   case AP
   of nil then Free
   [] X|Xr then
      case X
      of ident(F) then
	 local NewFree in
	    NewFree={Dictionary.clone Free}
	    if {List.member ident(F) Bound} then skip else {Dictionary.put NewFree F {EnvMap F Env} } end
	    {AddArgList Xr Env Bound NewFree}
	 end
      else
	 {AddArgList Xr Env Bound Free}
      end
   end
end

%=============================================================================================
%Find list of free variables

declare
fun {FindFree S Env Bound Free}
   %S should be a list!
   case S
   of X|Y then skip
   else raise stmerr(S) end
   end
   %Now check for statements
   case S
   of [nop] then Free
   [] [localvar ident(X) S1] then
      {FindFree S1 Env ident(X)|Bound Free}
   [] [bind X Y] then
      local NewFree in
	 NewFree={Dictionary.clone Free}
	 case X
	 of ident(F) then if {List.member ident(F) Bound} then skip else {Dictionary.put NewFree F {EnvMap F Env} } end
	 else skip
	 end
	 case Y
	 of ident(F) then if {List.member ident(F) Bound} then skip else {Dictionary.put NewFree F {EnvMap F Env} } end
	 else skip
	 end
	 NewFree
      end
   [] [conditional ident(X) S1 S2] then
      local NewFree in
	 NewFree={Dictionary.clone Free}
	 if {List.member ident(X) Bound} then skip else {Dictionary.put NewFree X {EnvMap X Env} } end
	 {FindFree S1 Env Bound {FindFree S2 Env Bound NewFree} }
      end
   [] [match ident(X) P S1 S2] then
      local NewFree in
	 NewFree={Dictionary.clone Free}
	 if {List.member ident(X) Bound} then skip else {Dictionary.put NewFree X {EnvMap X Env} } end
	 {FindFree S1 Env Bound {FindFree S2 Env Bound NewFree} }
      end
   [] apply|ident(F)|AP then
      local NewFree in
	 NewFree={Dictionary.clone Free}
	 if {List.member ident(F) Bound} then skip else {Dictionary.put NewFree F {EnvMap F Env} } end
	 {AddArgList AP Env Bound NewFree}
      end
   else
      if S.2 \= nil then {FindFree S.1 Env Bound {FindFree S.2 Env Bound Free} }
      else {FindFree S.1 Env Bound Free}
      end
   end
end

%=============================================================================================
%Function to compute closure for procedures

declare
fun {Closure FP B Env}
   local Free RE in
      Free={Dictionary.new}
      RE={FindFree B Env FP Free}
      [procedure FP B RE]
   end
end

%=============================================================================================
%Pair matching for record with pattern.
%Compare features and their values

declare
fun {RecPairsCompWithVal P1 P2}
   local RecPairsCompWithValAux in
      fun {RecPairsCompWithValAux Xs Ys SoFar}
	 case Xs
	 of nil then
	    case Ys
	    of nil then SoFar
	    else false
	    end
	 [] X|Xr then
	    case Ys
	    of nil then false
	    [] Y|Yr then
	       case X.1#Y.1
	       of literal(A)#literal(B) then
		  if A == B then
		     case Y.2.1
		     of literal(N) then
			case X.2.1
			of literal(M) then
			   if M == N then {RecPairsCompWithValAux Xr Yr SoFar}
			   else {RecPairsCompWithValAux Xr Yr false}
			   end
			[] ident(Var) then
			   %This Variable should be bound to literal(N), else false
			   local Val in
			      Val = {GetValFromSAS Var}
			      case Val
			      of literal(M) then
				 if M == N then {RecPairsCompWithValAux Xr Yr SoFar}
				 else {RecPairsCompWithValAux Xr Yr false}
				 end
			      else {RecPairsCompWithValAux Xr Yr false}
			      end
			   end
			end
		     else {RecPairsCompWithValAux Xr Yr SoFar}
		     end
		  else {RecPairsCompWithValAux Xr Yr false}
		  end
	       else
		  raise illegalRecord(Xs) end
	       end
	    end
	 end
      end
      {RecPairsCompWithValAux P1 P2 true}
   end
end

%=============================================================================================
%Pattern matching for records

declare
fun {PatternMatch E1 E2}
   case E1
   of [record literal(R1) P1] then
      case E2
      of [record literal(R2) P2] then
	 if R1 \= R2 then false
	 else
	    if { RecPairsCompWithVal {SortRecordPairs P1} {SortRecordPairs P2} } == true then true
	    else false
	    end
	 end
      else
	 false
      end
   else
      false
   end
end

%=============================================================================================
%Add Pattern to Environment
%Returns an environment with the variables added

declare
fun {AddPatternToEnv P Env}
   case P
   of H|T then {AddPatternToEnv T {AddPatternToEnv H Env}}
   [] ident(X) then
      local NE in
	 NE={Dictionary.clone Env}
	 {Dictionary.put NE X {GetID}}
	 {SASAdd {Dictionary.get NE X}}
	 NE
      end
   else
      Env
   end
end

%=============================================================================================
%Bind formal parameters to actual parameters

declare
proc {BindFTOA FP AP}
   case FP
   of nil then skip
   [] F|Fr then
      case AP
      of nil then skip
      [] A|Ar then
	 {UnifySAS F A}
	 {BindFTOA Fr Ar}
      end
   else
      skip
   end
end

%=============================================================================================
%Procedure for printing the SAS given an environment

declare
proc {DispSAS E}
   case E
   of nil then skip
   [] V#K|Xr then
      {Browse V}
      {Browse {GetValFromSAS K}}
   end
end

%=============================================================================================
%Main Interpreter

declare
proc {Interpret S}
   local Env Run in
      proc {Run S E}
	 {Browse 'Currently Executing Statement'}
	 {Browse S}
	 {Browse 'Environment'}
	 {Browse {Dictionary.entries E}}
	 {Browse 'Values in SAS'}
	 {DispSAS {Dictionary.entries E}}
	 {Browse '==============================' }
         %If S is not a list, then there is a syntax error 
	 case S
	 of X|Y then skip
	 else raise stmerr(S) end
	 end
         %Try and search for valid syntax, else consider it as a sequence of statements
	 case S
	 of [nop] then skip
	 [] [localvar ident(X) S1] then
	    local NE in
	       NE={Dictionary.clone E}
	       {Dictionary.put NE X {GetID}}
	       {SASAdd {Dictionary.get NE X}}
	       {Run S1 NE}
	    end
	 [] [bind X Y] then
            %Unify the two expressions in the SAS (if it is a procedure, compute closure)
	    local ToBindX ToBindY in
	       case X
	       of [procedure FP B] then ToBindX={Closure FP B E}
	       else ToBindX={IdenMap X E}
	       end
	       case Y
	       of [procedure FP B] then ToBindY={Closure FP B E}
	       else ToBindY={IdenMap Y E}
	       end
	       {UnifySAS ToBindX ToBindY}
	    end
	 [] [conditional ident(X) S1 S2] then
	    local XSAS in
	       XSAS = {GetValFromSAS {EnvMap X E}}
	       if XSAS==unBOUND then raise unbnd(X) end
	       else
		  if XSAS==literal(t) then {Run S1 E}
		  else
		     if XSAS==literal(f) then {Run S2 E}
		     else raise wrongtype(X) end
		     end
		  end
		  skip
	       end  
	    end
	 [] [match ident(X) P S1 S2] then
	     local XSAS in
	       XSAS = {GetValFromSAS {EnvMap X E}}
	       if XSAS==unBOUND then raise unbnd(X) end
	       else
		  if {PatternMatch XSAS P} == true then
		     local NE in
			NE={AddPatternToEnv P E}
			{UnifySAS XSAS {IdenMap P NE}}
			{Run S1 NE}
		     end
		  else
		     {Run S2 E}
		  end
	       end  
	     end
	 [] apply|ident(F)|AP then
	    local FSAS in
	       FSAS = {GetValFromSAS {EnvMap F E}}
	       if FSAS==unBOUND then raise unbnd(F) end
	       else
		  case FSAS
		  of [procedure FP B RE] then
		     %Check if same parity
		     if {List.length FP} \= {List.length AP} then raise illarr({List.length FP} {List.length AP}) end
		     else
			local NewEnv in
			   NewEnv={AddPatternToEnv FP RE}
			   {BindFTOA {IdenMap FP NewEnv} {IdenMap AP E}}
			   {Run B NewEnv}
			end
		     end
		  else raise cantapp(FSAS) end
		  end
	       end
	    end
	 else
            %It is a sequence of statements
	    {Run S.1 E}
	    if S.2 \= nil then
	       {Run S.2 E}
	    end
	 end
      end
      Env={Dictionary.new}
      {Run S Env}
   end
end

%=============================================================================================
%Try Programs

try
   %{Interpret [localvar ident(x) [ [nop] [conditional ident(x) [nop] [nop]] ]]}
   %{Interpret [localvar ident(x) [ [localvar ident(x) [  [localvar ident(x) [nop]] [nop] [nop] ] ] [nop]  [nop]] ]}
   {Interpret [
	       [localvar ident(x) [
				  [
				   localvar ident(y) [
						      [
						       localvar ident(z) [
									  localvar ident(rec) [
											       localvar ident(pr) [
									  [bind ident(x) [record literal(a) [ [literal(f2) ident(x)] [literal(f1) ident(z)] ] ]]
														   [bind ident(y) [record literal(a) [ [literal(f1) ident(z)] [literal(f2) ident(y)] ] ]]
														   [bind ident(x) ident(y)]
														   [bind ident(rec) literal(f)]
									  [match ident(x) [record literal(a) [ [literal(f2) ident(q)] [literal(f1) ident(b)] ] ] [nop] [nop] ]
									  [bind ident(pr) [procedure [ident(p) ident(q)] [
															 
															 [localvar ident(y) [
																	     [bind ident(p) ident(y)]
																	    ] ]
															[conditional ident(rec) [ [apply ident(pr) ident(p) literal(40)]] [[bind ident(y) ident(y) ]  ] ]
															 ] ] ]
														   [localvar ident(rec) [
																	 [bind ident(rec) literal(t)]
									  [apply ident(pr) ident(rec) ident(x)]]
											      ]]]
									  ]
						      ]
						      [nop]
						      [nop]
						      [nop]
						     ]
				  ]
				  [nop]
				  [nop]
				  ]]
	       [nop]
	      ]
   }
   %{Interpret [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]]}
   %{Interpret [localvar ident(x) [localvar ident(y) [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]]]]}
catch Err then
   case Err
   of stmerr(X) then {Browse X} {Browse 'Above is not a statement.'}
   [] varndec(X) then {Browse X} {Browse 'Above identifier has not been declared.'}
   [] cantapp(X) then {Browse X} {Browse 'Above value is not a procedure. Hence cannot be applied'}
   [] illarr(X Y) then {Browse X} {Browse Y} {Browse 'Illegal Arity. Above do not match.' } 
   [] wrongtype(X) then {Browse X} {Browse 'Above identifier should be true/false because it is used in if.'}
   [] unbnd(X) then {Browse X} {Browse 'Above variable was unbound at time of usage. Hanging!'} local Hang in  proc {Hang}  {Hang} end  {Hang} end %We do not have paraller programming for now, hence we hang.
   [] typemis(X Y) then {Browse X} {Browse Y} {Browse 'Illegal Unification of the above two values. Type mismatch'}
   [] illass(X Y) then {Browse X} {Browse Y} {Browse 'Illegal Unification of the above two values. Unequal Values'}
   [] procmis(X Y) then {Browse X} {Browse Y} {Browse 'Illegal unification of two procedures!'}
   [] illegalRecord(Pairs) then {Browse Pairs} {Browse 'Illegal Record Value' }
   else {Browse 'Unidentified Exception!!'}
   end
   {Browse 'Error! Exiting...'}
finally
   {Browse 'Thank you for using our interpreter' }
end

%=============================================================================================
