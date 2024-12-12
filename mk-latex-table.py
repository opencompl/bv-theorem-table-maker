#!/usr/bin/env python3
import json
import pandas as pd
import sys
import argparse
import csv

from multiprocessing import Pool

# Function to fetch data from the API
def fetch_data(query):
    print(f"[INFO]: fetching {query}", file=sys.stderr)
    url = f"http://localhost:8088/json?q={query}"
    response = requests.get(url, verify=False)
    return response.json()

# Function to get the cell data for a specific row and column
def get_cell_data(row_col_pair):
    row_name, col_name = row_col_pair
    # --query = f"{row_name},{col_name}"
    query = "BitVec." + row_name[7:] + "_" + col_name[7:]
    data = fetch_data(query)
    if 'hits' in data:
        return True
    else:
        return False


# Function to generate the LaTeX table
def generate_latex_table():
    """
    Make a latex table, given the CSV file:

    ```
        accessor function  doesExist
    0      toNat      add       True
    1      toInt      add       True
    2      toFin      add       True
    3    getElem      add      False
    4    getLsbD      add      False
    ..       ...      ...        ...
    226    toFin   twoPow      False
    227  getElem   twoPow       True
    228  getLsbD   twoPow       True
    229  getMsbD   twoPow       True
    230      msb   twoPow       True


            accessor function-add  function-sub
    0      toNat      true       false ...

    ```
    """

    # load file
    df = pd.read_csv('theorem-table.csv')
    unique_accessors = df['accessor'].unique()
    unique_functions = df['function'].unique()


    # Create the header row
    latex_table = "\\hspace{-2em}"
    latex_table += "\\begin{tabular}{|l|" + "C|" * len(unique_functions) + "}\n"
    latex_table += "\\hline\n"
    latex_table += " & \\tablerotate{" + "} & \\tablerotate{".join(unique_functions)+ "} \\\\\n"
    latex_table += "\\hline\n"

    exists_acc_fun = set()

    print(df)

    for (_, row) in df.iterrows():
        print(f"row: {row}")
        if row['doesExist']:
            exists_acc_fun.add((row['accessor'], row['function']))

    for acc in unique_accessors:
        latex_table += acc[7:]
        for fun in unique_functions:
            does_exist = (acc, fun) in exists_acc_fun
            latex_table += " & " + ('\\tableok' if does_exist else '\\tableno')
        latex_table += " \\\\\n"
        latex_table += "\\hline\n"

    return latex_table

    # # Fill in the table rowsd
    # df.sort_values(by=accessor)
    # df.piv
    # for row in df:
    #     latex_table += row['accessor'][7:]
    #     for j in range(len(columns)):
    #         latex_table += " & " + ('\\tableok' if cell_data[i * len(columns) + j] else '\\tableno')
    #     latex_table += " \\\\\n"
    #     latex_table += "\\hline\n"

    # latex_table += "\\end{tabular}"
    return latex_table

smtlib_functions = ['add', 'sub', 'neg', 'abs', 'mul', 'udiv', 'urem', 'sdiv',
        'srem', 'smod', 'umod', 'ofBool', 'fill', 'extract', 'extractLsb\'',
        'zeroExtend', 'shiftLeftZeroExtend', 'zeroExtend\'', 'signExtend',
        'and', 'or', 'xor', 'not',  'shiftLeft', 'ushiftRight', 'sshiftRight',
        'sshiftRight\'', 'rotateLeft', 'rotateRight', 'append', 'replicate',
        'concat', 'twoPow' ]

std_functions = ['toNat', 'toInt', 'toFin',
        'getElem', 'getLsbD', 'getMsbD', 'msb']

def get_functions(names):
    res = []
    for name in names:
        if name == 'getElem':
            name = "getLsb'"
        fullname = "BitVec." + name
        result = fetch_data(fullname)
        if 'hits' in result:
            for hit in result['hits']:
                if hit['name'] == fullname:
                    if name == "getLsb'":
                        hit['name'] = "BitVec.getElem"

                    res.append(hit)
    return res

# columns = get_functions(smtlib_functions) # smt operations.
# rows = get_functions(std_functions) # # getMsbD, ... (Accessors)


parser = argparse.ArgumentParser()

parser.add_argument('-t', '--tex',
                    action='store_true')  # on/off flag

args = parser.parse_args()

# if args.tex:
table = generate_latex_table()
# else:
#     table = generate_markdown_table(rows, columns)
print(table)
with open("bitvec_functions.tex", "w") as f:
    f.write(table)
