"""
Programa para comparar o resultado do programa com o resultado esperado
Necessário ter o arquivo fullTest.sml e suas dependências em ordem, assim como
o arquivo com o output esperado para comparacao

Eu ACHO que o operador > não funciona no windows, adapte para usar o equivalente do Powershell e 
redirecionar a saida para um arquivo (ou o que da problema é o "<"? Não lembro)



Autor: Diogo Neiss
"""

import os
import subprocess


# como ele faz append necessario apagar o arquivo antes de executar
if os.path.isfile("Plc-Output"):
    os.remove("Plc-Output")

# salva a saida da execução no arquivo output.txt
subprocess.call('sml ./fullTest.sml > output.txt', shell=True)


#coloca aqui o nome do arquivo que voce salvou o gabarito
expected = open("Expected-Output", "r").readlines()
actual = open("Plc-Output", "r").readlines()

failures = 0
for i in range(len(expected)):
    if expected[i] != actual[i]:
        failures += 1
        print(f"Line {str(i+1)}:\n\tExpected: {expected[i]}\tActual:  {actual[i]}")
        print("___________")
        
if failures == 0:
    print("All tests passed!")
else:
    print("Total of " + str(failures) + " failures.")
        