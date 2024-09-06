from pysat.formula import CNF
from pysat.solvers import Solver

def encode_problem_es3(tasks, resources):
    cnf = CNF()
    max_time = max(task[2] for task in tasks)

    # Variables u[i][j] for task i accessing resource j
    u = [[i * resources + j + 1 for j in range(resources)] for i in range(len(tasks))]

    # Variables z[i][t] for task i accessing some resource at time t
    z = [[len(tasks) * resources + i * max_time + t + 1 for t in range(max_time)] for i in range(len(tasks))]

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

    # C3: Non-preemptive resource access
    for i in range(len(tasks)):
        for t in range(tasks[i][0], tasks[i][2] - tasks[i][1]):
            # If task i is accessing a resource at time t and t+1, it must be the same resource
            clause = [-z[i][t], -z[i][t+1]]
            clause_str = [f"-z{i+1}{t} -z{i+1}{t+1}"]
            for j in range(resources):
                cnf.append([-z[i][t], -z[i][t+1], -u[i][j], u[i][j]])
                clause.append(u[i][j])
            cnf.append(clause)

        # Ensure that the task accesses the resource for its entire duration
        for t in range(tasks[i][0], tasks[i][2] - tasks[i][1] + 1):
            clause = [-z[i][t]]
            for k in range(1, tasks[i][1]):
                if t + k < tasks[i][2]:
                    clause.append(z[i][t+k])
            cnf.append(clause)

    # Link u and z variables
    for i in range(len(tasks)):
        for j in range(resources):
            for t in range(tasks[i][0], tasks[i][2]):
                cnf.append([-u[i][j], -z[i][t], z[i][t]])
                cnf.append([u[i][j], z[i][t], -z[i][t]])

    return cnf, max_time, u, z

# Example usage
tasks = [(0, 2, 2), (0, 2, 3)]  # Each task is a tuple (ri, ei, di)
resources = 2
cnf, max_time, u, z = encode_problem_es3(tasks, resources)

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
            for t in range(max_time):
                if model[z[i][t] - 1] > 0:
                    print(f"Task {i} is accessing a resource at time {t}")
    else:
        print("No solution found")