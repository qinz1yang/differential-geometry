-- Permit long Lean identifiers to wrap without changing their displayed text.
function Code(el)
  if FORMAT ~= 'latex' then return nil end
  local out = {}
  local previous = ''
  for index, cp in utf8.codes(el.text) do
    local c = utf8.char(cp)
    if (c:match('%u') and previous:match('%l')) or
       (el.text:match('^[0-9a-f]+$') and index % 8 == 0) then
      table.insert(out, '\\allowbreak{}')
    end
    local escaped = ({['\\']='\\textbackslash{}',['{']='\\{',['}']='\\}',
      ['$']='\\$',['&']='\\&',['#']='\\#',['%']='\\%',
      ['~']='\\textasciitilde{}',['^']='\\textasciicircum{}',['_']='\\_'})[c] or c
    if c == '_' or c == '.' or c == '/' or c == '-' then
      escaped = escaped .. '\\allowbreak{}'
    end
    table.insert(out, escaped)
    previous = c
  end
  return pandoc.RawInline('latex', '{\\small\\texttt{' .. table.concat(out) .. '}}')
end
