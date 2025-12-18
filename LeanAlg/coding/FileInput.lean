
def path : System.FilePath := System.mkFilePath ["LeanAlg", "coding", "foo.txt"]

def f : IO String := IO.FS.readFile path

#eval f

