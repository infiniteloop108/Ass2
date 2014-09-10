%SAS is a dictionary which maps environment variables to a 2-element list.
%1st element of that list contains the parent (in the Disjoint Set Data Structure). 2nd elemet signifies whether it is bound or unbound
%To see the status of a variable you have to look at its root.

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
%{Dictionary.reset SAS}

%===========================
%{BindAdd 1}
%{BindAdd 2}
%{BindAdd 3}
%{Browse {RetrieveNodeSAS 1}}
%{Browse {Dictionary.entries SAS}}
%{UnifySAS 3 1}
%{Bindval 1 3}
%{Browse {RetrievefromSAS 3}}
%{Browse {Dictionary.entries SAS}}
%{Browse hello}
%=============================
%SAS finished
