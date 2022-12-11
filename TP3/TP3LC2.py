#!pip install pysmt
import pysmt.shortcuts 
import pysmt.typing 


# função que cria a "próxima variável" no sistema de transição
def following(x):
	return Symbol(f'{x.symbol_name()}_', x.symbol_type())

# função que cria um clone de uma variável para um determinado step
def next_(x, step):
	return Symbol(f"{x.symbol_name()}{step}", x.symbol_type())

#TODO change to SFOTS
# classe que representa um FOTS
class FOTS:

        """
        Construtor do FOTS
        
        Parâmetros:
            - label : indica o nome do conjunto das variáveis pertencentes a este FOTS.
                      De acordo com os apontamentos, seria equivalente a 'X'.
            
            - variables: uma lista que representa o conjunto das variáveis do FOTS.
                         Ao ser construído, o FOTS transforma todas as variáveis deste conjunto
                         num clone com a label atrás. Por exemplo, se passarmos  a label 'X' e o conjunto [z, pc],
                         o que o FOTS guarda é o conjunto [X_z, X_pc]
            
            - init: Predicado do estado inicial. Assume-se que usa um subconjunto das variáveis do FOTS.
                    O FOTS faz automaticamente a conversão das variáveis para a versão com label.

            - trans: Predicado da relação de transição. Assume-se que usa um subconjunto das variáveis do FOTS, e 
                     faz uso da função de following.
                     O FOTS faz automaticamente a conversão das variáveis para a versão com label.
        """
    def __init__(self, label, variables, init, trans, error):
        self.label = label

        self.create_variables(variables)	
        self.create_init(variables, init)
        self.create_trans(variables, trans)
        #TODO
        #self.error = self.create_error(variabels, error) 

    def create_variables(self, variables):
        self.variables = [ Symbol(f'{self.label}_{v.symbol_name()}', v.symbol_type()) for v in variables ]
        self.original_variables = variables

    def create_init(self, variables, init):
        self.init = init.substitute( { variables[i]: self.variables[i] for i in range(len(variables)) } )
        self.original_init = init

    def create_trans(self, variables, trans):
        subs = { variables[i]: self.variables[i] for i in range(len(variables)) }
        for v in variables:
            v = following(v)
            subs[v] = Symbol(f'{self.label}_{v.symbol_name()}', v.symbol_type())

        self.trans = trans.substitute(subs)
        self.original_trans = trans

    #TODO
    def create_error(self, variables, error):
        pass
    
    # função que retorna um dicionário de substituições com os clones de um determinado estado
    def get_substitutes(self, i):
        subs = {}
        for v in self.variables:
            subs[v] = next_(v, i)
            subs[following(v)] = next_(v, i+1)
        return subs

    def get_vars(self, i):
        return [next_(v, i) for v in self.variables]

    # função que retorna o estado inicial do FOTS
    def get_init(self):
        subs = self.get_substitutes(0)
        return self.init.substitute(subs)

    # função que retorna o predicado de transição num certo estado
    def get_trans(self, state):
        subs = self.get_substitutes(state)
        return self.trans.substitute(subs)

    # função que returna a expansão do predicado de transição para k passos
    def expand_trans(self, k):
        # T(0,1) /\ ... /\ T(k-1, k)
        return And([self.get_trans(i) for i in range(k)])


    ## Funções para propriedades

    # função que recebe uma propriedade e muda as variáveis para a sua versão com label
    def parse_prop(self, prop):
        subs = { v: Symbol(f'{self.label}_{v.symbol_name()}', v.symbol_type()) for v in prop.get_free_variables() }

        return prop.substitute(subs)

    # função que retorna uma propriedade num certo estado
    def get_prop(self, prop, state):
        subs = self.get_substitutes(state)
        return prop.substitute(subs)

    # função que expande uma propriedade para k passos
    def expand_prop(self, prop, k):
        # P(0) /\ P(1) /\ ... /\ P(k) 
        return And([self.get_prop(prop, i) for i in range(k+1)])       


    def check_property(self, prop, k):
        prop = self.parse_prop(prop)
        return self.k_induction(prop, k)


    def k_induction(self, prop, k):
        I = self.get_init()
        Tk_1 = self.expand_trans(k-1)
        Pk_1 = self.expand_prop(prop, k-1)

        r = is_sat(And(I, Tk_1, Not(Pk_1)))
        if r: print("Invalid property")
        Pk = self.expand_prop(prop, k-1)
        Tk = self.expand_trans(k)
        Pk1 = self.expand_prop(prop, k)

        r = get_model(And(Pk, Tk, Not(Pk1)))
        if r: 
            print(r)
            print("Invalid property")
