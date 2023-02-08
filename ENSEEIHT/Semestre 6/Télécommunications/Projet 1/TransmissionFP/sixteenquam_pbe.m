clear all
close all
%% ------------------------ 16-QAM -------------------------- %%

%% Génération de l%information binaire
M = 16;
n=1600;
bits = randi([0,1], 1, n);
dataIn = bits';

fp = 2000; %Hz fréquence porteuse
fe = 10000; %Hz fréquence d'échantillonnage
Rb = 2000;%48000
TEB_th = 10^(-2);
Te = 1/fe;
Tb = 1/Rb; %période binaire
Rs = Rb/log2(M); %débit symbole
Ts = 1/Rs; %période symbole
Ns = Ts*fe; %facteur de suréchantillonnage
EbN0dB = [0:6];

%% Filtre de cosinus surélevé
alpha = 0.5;
span = 5;
sps = 10;
h = rcosdesign(alpha, span, sps);

%% Mapping Symboles 16-aires à moyenne nulle 
d = bit2int(dataIn, log2(M)); % bits en décimal
s = [1+j 1-j -1-j -1+j 3+j 3-j -3-j -3+j 1+3j 1-3j -1-3j -1+3j 3+3j 3-3j -3-3j -3+3j]; 
dk = s(1)*(d==0) + s(2)*(d==1) + s(3)*(d==2) + s(4)*(d==3) + s(5)*(d==4) + s(6)*(d==5) + s(7)*(d==6) + s(8)*(d==7) ...
    + s(9)*(d==8) + s(10)*(d==9) + s(11)*(d==10) + s(12)*(d==11) + s(13)*(d==12) + s(14)*(d==13) + s(15)*(d==14) + s(16)*(d==15) ;

%% Constellation 
ak = real(dk);
bk = imag(dk);
figure('Name', "Constellation  16-QAM (bk = f(ak)) après mapping");
plot(ak,bk,'linestyle','none','marker','o');
title( "Constellation  16-QAM (bk = f(ak)) après mapping");

%% Génération de la suite de Diracs pondérés par les symbols (suréchantillonnage)
a = kron(dk', [1 zeros(1,Ns-1)]); 

%% Filtrage de mise en forme 
xe = filter(h,1,[a zeros(1,length(h))]);

%% DSP
[DSP,f] = pwelch(xe,[],[],[],fe,"twosided");
figure;
semilogy(DSP);
title("DSP (16-QAM) sans bruit");

%% x <- xe
x=xe;

%% Filtrage de réception
z = filter(h,1,x); 

%% Echantillonnage 
zm=z(length(h)+1:Ns:length(z));
zm=real(zm)-imag(zm)*j;

%% Démapping
r = real(zm);
i = imag(zm) ;
pr1 = 0<=r & r<2;
pi1 = 0<=i & i<2;
pr3 = 2<=r & r<4;
pi3 = 2<=i & i<4;
nr1 = r<0 & r>=-2;
ni1 = i<0 & i>=-2;
nr3 = r<-2 & r>=-4;
ni3 = i<-2 & i>=-4;

tmp = (pr1&pi1) * 0 + (pr1&ni1) * 1 + (nr1&ni1) * 2 + (nr1&pi1) * 3 ...
 + (pr3&pi1) * 4 + (pr3&ni1) * 5 + (nr3&ni1) * 6 + (nr3&pi1) * 7 ...
 + (pr1&pi3) * 8 + (pr1&ni3) * 9 + (nr1&ni3) * 10 + (nr1&pi3) * 11 ...
 + (pr3&pi3) * 12 + (pr3&ni3) * 13 + (nr3&ni3) * 14 + (nr3&pi3) * 15;

bits_recus = de2bi(tmp, 4);
tmp2 = [bits_recus(:,4) bits_recus(:,3) bits_recus(:,2) bits_recus(:,1)];
bits_recus_final = [];
for i=1:length(bits_recus(:,1))
    bits_recus_final = [bits_recus_final tmp2(i,:)];
end
%% TEB
TEB = sum(bits~=bits_recus_final);
if sum(bits~=bits_recus_final)==0
    disp('TEB = 0 (Modulation 16-QAM - sans bruit)');
end
%% ------------------------------------------------------- %%

%% -------------------- Ajout du bruit ------------------- %%
figure('Name', "Constellation  16-QAM (bk = f(ak)) en sortie de l'échantillonage");

Puissance_recu = mean(abs(x).^2);
TEB_bruite_matrice = zeros(1,7);
TEB_theorique_matrice = zeros(1,7);
for k = 0:6
    EbN0 = 10^(k/10);
    sigma_n = sqrt((Puissance_recu*Ns)/(2*log2(M)*(EbN0)));
    bruit = sigma_n * randn(1, length(x)) + j*sigma_n * randn(1, length(x));
    
    x_bruite = x + bruit;


    %% Filtre de réception
    hr = fliplr(h);
    z_bruite = filter(hr,1,x_bruite);

    %% Echantillonage
    zm_bruite=z_bruite(length(h)+1:Ns:length(z_bruite));
    zm_bruite=real(zm_bruite)-imag(zm_bruite)*j;

    %% Constellation
    if k<6
        pos = k+1;
    else
        pos =8;
    end
    ak =real(zm_bruite);
    bk= imag(zm_bruite);
    subplot(3,3,pos);
    plot(ak,bk,'linestyle','none','marker','o');
    title('EbN0dB = ' , num2str(k));

    %% Démapping
    r = real(zm_bruite);
    i = imag(zm_bruite) ;
    pr1 = 0<=r & r<2;
    pi1 = 0<=i & i<2;
    pr3 = 2<=r & r<4;
    pi3 = 2<=i & i<4;
    nr1 = r<0 & r>=-2;
    ni1 = i<0 & i>=-2;
    nr3 = r<-2 & r>=-4;
    ni3 = i<-2 & i>=-4;
    
    tmp_bruite = (pr1&pi1) * 0 + (pr1&ni1) * 1 + (nr1&ni1) * 2 + (nr1&pi1) * 3 ...
     + (pr3&pi1) * 4 + (pr3&ni1) * 5 + (nr3&ni1) * 6 + (nr3&pi1) * 7 ...
     + (pr1&pi3) * 8 + (pr1&ni3) * 9 + (nr1&ni3) * 10 + (nr1&pi3) * 11 ...
     + (pr3&pi3) * 12 + (pr3&ni3) * 13 + (nr3&ni3) * 14 + (nr3&pi3) * 15;
    
    bits_recus_bruite = de2bi(tmp_bruite, 4);
    tmp2_bruite = [bits_recus_bruite(:,4) bits_recus_bruite(:,3) bits_recus_bruite(:,2) bits_recus_bruite(:,1)];
    bits_recus_final_bruite = [];
    for j=1:length(bits_recus_bruite(:,1))
        bits_recus_final_bruite = [bits_recus_final_bruite tmp2_bruite(j,:)];
    end
    
    %% TEB
    erreur = sum(bits~=bits_recus_final_bruite);
    TEB_bruite = erreur/n;
    TEB_bruite_matrice(k+1) = TEB_bruite;
    if sum(bits~=bits_recus_final_bruite)==0
        disp('TEB = 0 (Modulation 16-QAM - avec bruit)');
    end

end
%% ------------------------------------------------------- %%
TEB_theorique_matrice = qfunc(sqrt(10.^(EbN0dB/10)));

%% DSP
[DSP,f] = pwelch(x_bruite,[],[],[],fe,"twosided");
figure;
semilogy(DSP);
title("DSP (16-QAM) avec bruit");

%% TEB simulé
figure;
semilogy(EbN0dB,TEB_bruite_matrice,'p--','LineWidth',3);
xlabel('E_b/N_0 (en dB)');
ylabel('TEB');
title('TEB simulé en fonction de EBN0dB ');
grid;


%% Comparaison du TEB simulé au TEB théorique de la chaine étudiée 
figure("Name", 'Comparaison TEB simulée et TEB théorique');
semilogy(EbN0dB,TEB_bruite_matrice,'p--','LineWidth',3);
hold on;
semilogy(EbN0dB,TEB_theorique_matrice);
legend('Simulée', 'Théorique');
xlabel('Eb/No (dB)') ;
ylabel('TEB');
title('Comparaison TEB simulée et TEB théorique');

%% %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% FIN %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%% %%