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
	    [] Y|Yr then false
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
		     else
			%Exp1 is a procedure
			case Exp2
			of literal(Y) then raise typemis(Exp1 Exp2) end
			[] [record literal(R2) P2] then raise typemis(Exp1 Exp2) end
			else raise procmis(Exp1 Exp2) end
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
fun {EnvMap Env X}
   %If it is not yet defined, then raise an exception
   if {Dictionary.member Env X}==false then raise varndec(X) end end
   %Return the mapped environment variable
   {Dictionary.get Env X}
end

%=============================================================================================
%Function to map an expression with identifiers with environment variables.

declare
fun {IdenMap Env V}
   case V
   of H|T then {IdenMap Env H}|{IdenMap Env T}
   [] ident(X) then ident({EnvMap Env X})
   else V
   end
end

%=============================================================================================
%Closure for procedures
%How do you match a pattern to a procedure?

declare
fun {Closure Env P}
   P
end

%=============================================================================================
%Main Interpreter

declare
proc {Interpret S}
   local Env Run in
      proc {Run S E}
	 %{Browse S}
	 {Browse {Dictionary.entries E}}
         %If S is not a list, then there is a syntax error 
	 case S
	 of X|Y then skip
	 else raise stmerr(S) end
	 end
         %Try and search for valid syntax, else consider it as a sequence of statements
	 case S
	 of [nop] then skip
	 [] [localvar ident(X) S] then
	    local NE in
	       NE={Dictionary.clone E}
	       {Dictionary.put NE X {GetID}}
	       {SASAdd {Dictionary.get NE X}}
	       {Run S NE}
	    end
	 [] [bind X Y] then
            %Unify the two expressions in the SAS
	    {UnifySAS {IdenMap X E} {IdenMap Y E}}   
	 %[] [conditional ident(X) S1 S2] then
	  %  local XSAS in
	   %    XSAS = {GetValFromSAS {EnvMap E X}}
       	   %    %To clarify
	    %   if XSAS==unBOUND then raise unbnd(X) end
	    %   else
	%	  if XSAS then {Run S1 E}
	%	  else {Run S2 E} end
	 %      end
	  %  end
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
	       localvar ident(x) [
				  
				  [
				   localvar ident(y) [

						      [localvar ident(x) [
									  bind ident(x) [record literal(a) [ [literal(f1) literal(10)] [literal(f2) ident(y)] ] ]
									 ]
						      ]
						      [nop]
						      [nop]
						      [bind ident(x) [record literal(a) [ [literal(f1) literal(10)] [literal(f2) ident(y)] ] ] ]
						     ]
				  ]
				  [nop]
				  [nop]
				 ]

	      ]
   }
   %{Interpret [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]]}
   %{Interpret [localvar ident(x) [localvar ident(y) [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]]]]}
catch Err then
   case Err
   of stmerr(X) then {Browse X} {Browse 'Above is not a statement.'}
   [] varndec(X) then {Browse X} {Browse 'Above identifier has not been declared.'}
   [] unbnd(X) then {Browse X} {Browse 'Above variable was unbound at time of usage. Hanging!'} local Hang in  proc {Hang}  {Hang} end  {Hang} end %We do not have paraller programming for now, hence we hang.
   [] typemis(X Y) then {Browse X} {Browse Y} {Browse 'Illegal Unification of the above two values. Type mismatch'}
   [] illass(X Y) then {Browse X} {Browse Y} {Browse 'Illegal Unification of the above two variables. Unequal Values'}
   [] procmis(X Y) then {Browse X} {Browse Y} {Browse 'Illegal unification of two procedures!'}
   [] illegalRecord(Pairs) then {Browse Pairs} {Browse 'Illegal Record Value' }
   else {Browse 'Unidentified Exception!!'}
   end
   {Browse 'Error! Exiting...'}
finally
   {Browse 'Thank you for using our interpreter' }
end

%=============================================================================================
