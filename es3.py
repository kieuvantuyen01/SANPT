from pysat.formula import CNF
from pysat.solvers import Solver

def encode_problem_es3(tasks, resources):
    cnf = CNF()
    max_time = max(task[2] for task in tasks)

    # Variables u[i][j] for task i accessing resource j
    u = [[i * resources + j + 1 for j in range(resources)] for i in range(len(tasks))]

    # Variables z[i][t] for task i accessing some resource at time t
    z = [[len(tasks) * resources + i * tasks[i][2] + t + 1 for t in range(tasks[i][2])] for i in range(len(tasks))]

    # Variables D[i][j][t] for non-preemptive access of resource j by task i starting at time t
    D = [[[len(tasks) * (resources + max_time) + i * resources * max_time + j * max_time + t + 1 
          for t in range(max_time)] for j in range(resources)] for i in range(len(tasks))]

    # D1: Task i should not access two resources at the same time
    for i in range(len(tasks)):
        for j in range(resources):
            for jp in range(j + 1, resources):
                cnf.append([-u[i][j], -u[i][jp]])
                print(f"Added clause D1: -u{i+1}{j+1} -u{i+1}{jp+1}")

    # D2: Each task must get some resource
    for i in range(len(tasks)):
        # cnf.append([u[i][j] for j in range(resources)])
        # print(f"Added clause: u{i}0 u{i}1")
        clause = []
        clause_str = []
        for j in range(resources):
            clause.append(u[i][j])
            clause_str.append(f"u{i+1}{j+1}")
        cnf.append(clause)
        print(f"Added clause D2: {clause_str}")

    # D3: A resource can only be held by one task at a time
    for i in range(len(tasks)):
        for ip in range(i + 1, len(tasks)):
            for j in range(resources):
                for t in range(tasks[i][2]):
                    cnf.append([-z[i][t], -u[i][j], -z[ip][t], -u[ip][j]])
                    print(f"Added clause D3: -z{i+1}{t} -u{i+1}{j+1} -z{ip+1}{t} -u{ip+1}{j+1}")

    # D4: Each task must have exactly one start time for accessing a resource non-preemptively
    for i in range(len(tasks)):
        # cnf.append([D[i][j][t] for j in range(resources) for t in range(tasks[i][2] - tasks[i][1] + 1)])
        # print(f"Added clause D4: D{i}{j}{t}")
        clause = []
        clause_str = []
        for j in range(resources):
            for t in range(tasks[i][2] - tasks[i][1] + 1):
                clause.append(D[i][j][t])
                clause_str.append(f"D{i+1}{j+1}{t}")
        cnf.append(clause)
        print(f"Added clause D4: {clause_str}")

    # D5: Linking start variable to z and u variables
    for i in range(len(tasks)):
        for j in range(resources):
            for t in range(tasks[i][0], tasks[i][2] - tasks[i][1] + 1):
                # If D[i][j][t] is true, the task must hold the resource for its entire duration
                for tp in range(t, t + tasks[i][1]):
                    if tp < max_time:
                        cnf.append([-D[i][j][t], z[i][tp]])
                        print(f"Added clause: -D{i+1}{j+1}{t} z{i+1}{tp}")
                cnf.append([-D[i][j][t], u[i][j]])
                print(f"Added clause D5: -D{i+1}{j+1}{t} u{i+1}{j+1}")

                # If D[i][j][t] is true, the task must not hold the resource before t
                for tp in range(tasks[i][0], t):
                    cnf.append([-D[i][j][t], -z[i][tp]])
                    print(f"Added clause D5: -D{i+1}{j+1}{t} -z{i+1}{tp}")

                # If D[i][j][t] is true, the task must not hold the resource after t + e_i - 1
                for tp in range(t + tasks[i][1], tasks[i][2]):
                    if tp < max_time:
                        cnf.append([-D[i][j][t], -z[i][tp]])
                        print(f"Added clause D5: -D{i+1}{j+1}{t} -z{i+1}{tp}")
                        
                # Reverse implication
                clause = [D[i][j][t]]
                clause.extend([-u[i][j]])
                # clause.extend([-z[i][tp] for tp in range(t, min(t + tasks[i][1], max_time))])
                # cnf.append(clause)
                clause_str = []
                clause_str.append(f"D{i+1}{j+1}{t}")
                clause_str.append(f"-u{i+1}{j+1}")
                for tp in range(t, min(t + tasks[i][1], max_time)):
                    clause.append(-z[i][tp])
                    clause_str.append(f"-z{i+1}{tp}")
                cnf.append(clause)
                print(f"Added clause D5: {clause_str}")
    return cnf, max_time, u, z, D

# Example usage
tasks = [(0, 2, 2), (0, 2, 3)]  # Each task is a tuple (ri, ei, di)
resources = 2
cnf, max_time, u, z, D = encode_problem_es3(tasks, resources)

with Solver(name="glucose4") as solver:
    solver.append_formula(cnf.clauses)
    result = solver.solve()
    if result:
        model = solver.get_model()
        print("Satisfiable")
        for i in range(len(tasks)):
            for j in range(resources):
                if model[u[i][j] - 1] > 0:
                    print(f"Task {i} is assigned to resource {j}")
            for t in range(tasks[i][2]):
                if model[z[i][t] - 1] > 0:
                    print(f"Task {i} is accessing a resource at time {t}")
            for j in range(resources):
                for t in range(tasks[i][0], tasks[i][2] - tasks[i][1] + 1):
                    if model[D[i][j][t] - 1] > 0:
                        print(f"Task {i} starts non-preemptive access of resource {j} at time {t}")
    else:
        print("No solution found")