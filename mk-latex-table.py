#!/usr/bin/env python3
import json
import pandas as pd
import sys
import argparse
import csv

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
        if row['doesExist']:
            exists_acc_fun.add((row['accessor'], row['function']))

    for acc in unique_accessors:
        latex_table += acc
        for fun in unique_functions:
            does_exist = (acc, fun) in exists_acc_fun
            latex_table += " & " + ('\\tableok' if does_exist else '\\tableno')
        latex_table += " \\\\\n"
        latex_table += "\\hline\n"

    latex_table += "\\end{tabular}"
    return latex_table

if __name__ == "__main__":
    with open("bitvec_functions.tex", "w") as f:
        table = generate_latex_table()
        f.write(table)
