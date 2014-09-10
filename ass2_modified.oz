%==============================
% declaring dictionary for SAS
declare
SAS = {Dictionary.new}

%===============================
% Add a new value in SAS
declare
proc {BindAdd X}
   {Dictionary.put SAS X [X unBOUND]}
end

%===============================
% Function for getting parent node in equivalence class

declare
fun {RetrieveNodeSAS Exp1}
   local Node in
      Node={Dictionary.get SAS Exp1}
      if Node.1==Exp1 then Node
      else {RetrieveNodeSAS Node.1}
      end
   end
end

%==============================
% function for getting value of a variable

declare
fun {RetrievefromSAS Exp1}
   local Node in
      Node={RetrieveNodeSAS Exp1}
      Node.2.1
   end
end

%================================
% Unifying two variables

declare
proc {UnifySAS Exp1 Exp2}

   {Browse {Dictionary.entries SAS}}
   local NodeX NodeY in
      NodeX = {RetrieveNodeSAS Exp1}
      NodeY = {RetrieveNodeSAS Exp2}
      case NodeX.2.1
      of unBOUND then
	 {Dictionary.put SAS NodeX.1 [NodeY.1 unBOUND]}
      else case NodeY.2.1
	   of unBOUND then {Dictionary.put SAS NodeY.1 [NodeX.1 unBOUND]}
	   else case NodeX.2.1 == NodeY.2.1
		of true then
		   {Dictionary.put SAS NodeX.1 [NodeY.1 unBOUND]}
		   {Dictionary.put SAS NodeY.1 [NodeY.1 NodeY.2.1]}
		[] false then
		   {Browse "Illegal assignment"}
		end
	   end
      end
   end
end

%===============================
% Binding a variable

declare
proc {Bindval Exp Val}
   local NodeX in
      NodeX={RetrieveNodeSAS Exp}
      {Browse NodeX.2.1}
      case NodeX.2.1
      of unBOUND then {Dictionary.put SAS NodeX.1 [NodeX.1 Val]} {Browse hi}
      else case NodeX.2.1==Val
	   of true then skip
	   [] false then {Browse 'Illegal assignment'}
	   end
      end
   end
end

%===========================
% Reset SAS
%
{Dictionary.reset SAS}

%===========================
%{BindAdd 1}
%{BindAdd 2}
%{BindAdd 3}

%{Browse {RetrieveNodeSAS 1}}

%{Browse {Dictionary.entries SAS}}

{UnifySAS 3 1}
%{Bindval 1 3}
%{Browse {RetrievefromSAS 3}}
{Browse {Dictionary.entries SAS}}

{Browse hello}
declare
Env={Dictionary.new}

declare
TotVar={NewCell 0}

declare
fun {GetID}
   TotVar:=@TotVar+1
   @TotVar
end

declare
fun {EnvMap Env X}
   {Dictionary.get Env X}
end

declare
proc {Run S E}
   {Browse S}
   {Browse {Dictionary.entries E}}
   %If S is not a list, then there is a syntax error 
   case S
   of X|Y then skip
   else {Browse 'Compile Error'}
   end
   %Try and search for valid syntax, else consider it as a sequence of statements
   case S
   of [nop] then skip
   [] [localvar ident(X) S] then
      local NE in
	 NE={Dictionary.clone E}
	 {Dictionary.put NE X {GetID}}
	 {BindAdd {Dictionary.get NE X}}
	 {Run S NE}
      end
   [] [bind ident(X) ident(Y)] then
      % error if variable x or y is not declared
      if {Dictionary.member E X}==false then {Browse 'Variable not declared'}
      elseif {Dictionary.member E Y}==false then {Browse 'Variable not declared'}
      % otherwise unify the two in SAS
      else {UnifySAS {EnvMap E X} {EnvMap E Y}}
      end
   else
      %It is a sequence of statements
      {Run S.1 E}
      if S.2 \= nil then
	 {Run S.2 E}
      end
   end
end

{Run [localvar ident(x) [ [localvar ident(x) [  [localvar ident(x) [nop]] [nop] [nop] ] ] [nop]  [nop]] ] Env}

{Run [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]] Env}

{Browse {Dictionary.entries SAS}}
{Browse {Dictionary.entries Env }}

{Dictionary.reset SAS}
 
{Run [localvar ident(x) [localvar ident(y) [localvar ident(x) [localvar ident(y) [bind ident(x) ident(y)]]]]] Env}

%{Dictionary.put Env haha 2}
%{Browse {Dictionary.get Env haha}}