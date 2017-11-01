import os
import subprocess
#for each folder/sub-directory in the current directory that has the term 'batchlength' in its filename
loc=os.getcwd();#get current directory
subentries=os.listdir(loc);#folders and files in loc

z3path='C:\\Users\\Vidhya\\Documents\\z3-4.4.1-x86-win\\z3-4.4.1-x86-win\\bin\\.\z3.exe';

for subentry in subentries:#for each sub-entry in loc
#{
	batch_folder_path=os.path.join(loc,subentry);
	if ((os.path.isdir(batch_folder_path)) and ('batchlength' in subentry)):#if it is a directory and contains the term 'batchlength' in it name
	#{
		print("In folder:"+batch_folder_path);
		#create output file for storing z3 output
		outputfile_path=os.path.join(batch_folder_path,'z3output.txt');
		if os.path.exists(outputfile_path):#if such an output file already exits remove it and recreate it anew
		#{
			os.remove(outputfile_path);
			with open(outputfile_path,'w') as ofile:#open z3 output file
				ofile.write('In folder: '+batch_folder_path+'\n');
		#}
		files=os.listdir(batch_folder_path);#list of smt files in the batchfolder
		with open(outputfile_path,'a') as ofile:#open z3 output file
			#for each smt file in this folder that has the term 'altered' in items
			for file in files:
			#{
				if (('.smt2' in file) and ('altered' in file)):
				#{
					print('Running '+file+ ' on Z3\n');
					file_path=os.path.join(batch_folder_path,file);#file path is required to run on z3
					ofile.write('running '+file+ 'on Z3\n');
					#run file on z3 for 3 times
					for i in range(1,4,1):
					#{
						print('Run:'+str(i)+'\n');
						ofile.write('Run:'+str(i)+'\n');
						subprocess.call([z3path,file_path],stdout=ofile, stderr=ofile);
						print('Done');					
					#}
				#}
		#}
	#}
#}