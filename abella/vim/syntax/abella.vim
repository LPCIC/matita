syn region abellaComment start='/\*' end='\*/'

syn keyword abellaCommand Specification Import Quit Close
syn keyword abellaCommand Define Theorem by CoDefine Query Split as Set Show
syn match abellaCommand ":="
syn keyword abellaTactic induction on coinduction intros case search cut inst apply to backchain with unfold assert split left right permute monotone undo abort clear abbrev unabbrev
syn keyword abellaSkip skip

syn keyword abellaBinder forall nabla exists
syn match abellaConnective "/\\"
syn match abellaConnective "\\/"
syn match abellaConnective "->"
syn match abellaConnective "{"
syn match abellaConnective "|-"
syn match abellaConnective "}"

hi def link abellaComment Comment
hi def link abellaCommand Type
hi def link abellaTactic Statement
hi def link abellaBinder PreProc
hi def link abellaConnective PreProc
hi def link abellaSkip Todo
