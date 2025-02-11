import urllib.request 

for i in range(0, 100):
    name = f"D{i:02}"
    try:
        urllib.request.urlretrieve(f"http://www.bookuppro.com/ecopgn/{name}.pgn", f"/Users/hal/Documents/PythonScripts/Chess/Cython_test/opening_dl/{name}.pgn")
    except:
        next
    
