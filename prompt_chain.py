#The system can add number to the semantic types to distinguish the different semantic type nodes with the same name. For example: crm:E42_Identifier1, crm:E42_Identifier2, crm:E42_Identifier3 represent different semantic type nodes.
import os
import json

#The system can add number to the semantic types to distinguish the different semantic type nodes with the same name. For example: crm:E42_Identifier1, crm:E42_Identifier2, crm:E42_Identifier3 represent different semantic type nodes.
def generate_prompt_chain(train_data, test_data, model, ontologies, with_inst=False):
    """Generate a prompt chain for the LLM based on the table data and ontologies."""
    system_prompt = "You are a helpful assistant that can generate semantic graphs for tables in the format of JSON based on the ontologies given(delimited by '<Ontology>' and '</Ontology>') and the table data given(delimited by '<Table>' and '</Table>'). \
        In the Ontology part, nodes is delimited by '<Nodes>' and '</Nodes>', properties is delimited by '<Properties>' and '</Properties>', and potential triples is delimited by '<PotentialTriples>' and '</PotentialTriples>'. The symbol '->' in the ontology is used to represent the 'is parent class of' relation. \
        In the Table part, each table is a list of dictionaries, where each dictionary represents a row of the table, and the key-value pairs are the column names and their corresponding values."
    nodes = []
    properties = []
    potential_triples = []
    for ontology_name, ontology_data in ontologies.items():
        for node in ontology_data['Nodes']:
            nodes.append(node)
        for prop in ontology_data['Properties']:
            properties.append(prop)
        for triples in ontology_data['Potential triples']:
            potential_triples.append(triples.replace("<", "[").replace(">", "]"))   
    system_prompt += f"<Ontology> <Nodes> {nodes}</Nodes> \n <Properties> {properties}</Properties> \n <PotentialTriples> {potential_triples}</PotentialTriples></Ontology> \n"
    system_prompt += "You will solve the task by two steps: Step1(delimited by '<Step1>' and '</Step1>') Identify the appropriate semantic type and property for each column in the table. Step2(delimited by '<Step2>' and '</Step2>') Generate a semantic graph for the table. The solution are delimited by '<Solution>' and '</Solution>'.\n\
I will give you the examples of tables and the semantic graphs generated from the tables. The examples of tasks are delimited by '<Examples>' and '</Examples>'. \n"
    examples = "<Examples>"
    for example_data in train_data:
        examples += f"<Table> {example_data['table']} </Table>\n"
        examples += "<Solution>\n"
        examples += f"<Step1> {example_data['semantic_graph']['SetSemanticType']} </Step1>\n"
        examples += f"<Step2> {example_data['semantic_graph']['SetInternalLink']} </Step2>\n"
        examples += "</Solution>"
    examples += "</Examples>"
    system_prompt += examples
# 
# 2. Extract the column names and their corresponding row values from the lists of dictionaries. \n\
# 4. Rethink the internal links and the list of triples of semantic types and properties, change the unlogical part of internal links and list of triples of semantic types and properties. \n\
    chain_prompt_1 = "Step1 SetSemanticType: \n\
The system will first identify the appropriate semantic type and property for each column in the table. \n\
Solution Steps: \n\
1. Begin the response with 'Let's think step by step'. \n\
2. Following the reasoning steps, search the potential triples in the ontology to find the appropriate semantic types for each column in the table by reasoning the column name and the row values. All columns must be mapped to the Ontology. \
2. Following with reasoning steps, identify the appropriate semantic types from nodes in the ontology for each column in the table by reasoning the column name and the row values. All columns must be mapped to the Ontology. \
ONLY if all of the row values in the column are <Empty>, the system will take the column name into consideration to find the appropriate semantic types from nodes in the ontology. \n\
3. Find the appropriate properties from properties in the ontology to link the columns and the semantic types by reasoning the column names, the row values and the semantic types. \n\
4. The system will output the semantic types and properties in the format of a list of triples, where each triple has the form (subject, predicate, object). The subject is the semantic type, the predicate is the property, and the object is the column in the table.\
Please output the list of triples using <Step1> </Step1> tags in the format of in the Step1 of examples. For example: <Step1> [(semantic_type, property, column), (semantic_type, property, column), ...] </Step1>. "
    table  =f"<Table> {test_data} </Table>"
    chain_prompt_1 = chain_prompt_1 + table
    messages = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": chain_prompt_1}
    ]
    response = model.chat.completions.create(
    model="deepseek-chat",
    # model="gpt-3.5-turbo",
    messages=messages,
        stream=False, 
    )
    response_content = response.choices[0].message.content
    messages.append({"role": "assistant", "content": response_content})
    set_semantic_type = response_content.split("<Step1>")[1].split("</Step1>")[0]
    print(set_semantic_type)
#3. Review internal links and the list of triples of semantic types and properties, find the same semantic type which link to different internal nodes or the same internal node linked to different internal nodes. add a number to these semantic types and internal nodes to distinguish the different the nodes in the graph with the same name. \n\
#     chain_prompt_2 = " Let us do Step2 given the table and Step1. \n\
# Step2 Problem Statement: \n\
# Given the list of triples of semantic types and properties for the table(delimited by '<Step1>' and '</Step1>') and the original table, generate a semantic graph for the table. The semantic graph is a graph with nodes and edges. \
# The nodes are the semantic types or internal nodes in the ontology, and the edges are the properties that link between the nodes. Hint: 1. The graph is a tree structure. 2. The positions of the semantic types indicate the relationship between the semantic types and the internal nodes. \n\
# Solution: \n\
# 1. Begin the response with 'Let's think step by step'. \n\
# 2. Find the main root of the graph. The main root is the main entity which can represent the whole table. \n\
# 3. Search the potential triples in Ontology to find the appropriate internal nodes for the semantic types in Step1 to link to the root. You can replace the subject, object, predicate with their parent classes or subclasses in the potential triples to find the appropriate internal nodes for the semantic types in Step1. \n\
# 4. Review the internal links, find the isolated semantic types. And then go back to Step1 to find more suitbale semantic types to link to the root. \n\
# 5. Following with reasoning steps, find the appropriate properties for the internal links found in the previous step between the semantic types and the internal nodes. \n\
# Note: There always has one property between two nodes. Multiple properties between two nodes are not allowed in generating the semantic graph. \n\
# 6. Output the final internal links using <Step2> </Step2> tag in the format of in the Step2 of examples. For example: <Step2> [(internal_node, property, internal_node), (internal_node, property, semantic_type), (internal_node, property, internal_node), ...] </Step2>.\n"
#     chain_prompt_2 = chain_prompt_2 + f"<Step1> {set_semantic_type} </Step1>\n" + table
    chain_prompt_2 = "Step2 Problem Statement: Now that we have identified the semantic types and properties for each column, the next step is to establish internal links between these nodes based on the ontology. Note that the symbol '->' represents that the class or property before it is a subclass or subproperty of the one after it. \
This means that certain triples in the ontology may imply additional triples involving subclasses or subproperties. Your task is to identify and expand on these relationships when necessary. \
Solution Steps: \n\
1. Begin the response with 'Let's think step by step'. \n\
2. Review the semantic types and properties from Step 1, considering both direct triples and any implied triples. For example, if a triple <Class1, Property1, Class2> exists, and Class3 is a subclass of Class1, Property2 is a subproperty of Property1, and Class4 is a subclass of Class2, then the implied triple <Class3, Property2, Class4> should also be considered. \n\
3. When multiple paths exist between two nodes, prioritize paths that involve subclasses or subproperties, especially if they are more specific or contextually appropriate. \n\
4. Evaluate each possible relationship based on: - The subclass or subproperty hierarchy (indicated by '->'). - The frequency of the properties connecting the semantic types. - The context from the table data, such as proximity of related columns or co-occurrence patterns. \n\
5. Filter out implausible relationships using real-world logic and ensure that the relationships make sense within the domain ontology. For instance, a birth date should not be linked to an unrelated entity. \n\
6. Output the final internal links, including both direct and implied triples, using <Step2> tags in the format: <Step2> [(node1, property, node2), (node3, property, node4), ...] </Step2>. Make sure to include all logically consistent links, whether directly present in the ontology or implied by subclass and subproperty relationships. "
    chain_prompt_2 = chain_prompt_2 + f"<Step1> {set_semantic_type} </Step1>\n" + table
    messages2 = [
        {"role": "system", "content": system_prompt},
        {"role": "user", "content": chain_prompt_2}
    ]
    response = model.chat.completions.create(
        model="deepseek-chat",
        messages=messages2,
        stream=False,
    )
    response_content = response.choices[0].message.content
    messages.append({"role": "assistant", "content": response_content})
    return response_content, messages


#     2. Following the reasoning steps, search the potential triples whose subject is start with  in the ontology to find the appropriate semantic types for each column in the table by reasoning the column name and the row values. All columns must be mapped to the Ontology. \
# 2. Following with reasoning steps, identify the appropriate semantic types from nodes in the ontology for each column in the table by reasoning the column name and the row values. All columns must be mapped to the Ontology. \
# ONLY if all of the row values in the column are <Empty>, the system will take the column name into consideration to find the appropriate semantic types from nodes in the ontology. \n\
# 3. Find the appropriate properties from properties in the ontology to link the columns and the semantic types by reasoning the column names, the row values and the semantic types. \n\
# 4. The system will output the semantic types and properties in the format of a list of triples, where each triple has the form (subject, predicate, object). The subject is the semantic type, the predicate is the property, and the object is the column in the table.\
# Please output the list of triples using <Step1> </Step1> tags in the format of in the Step1 of examples. For example: <Step1> [(semantic_type, property, column), (semantic_type, property, column), ...] </Step1>. "
#     table  =f"<Table> {test_data} </Table>"